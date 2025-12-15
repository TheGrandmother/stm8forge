import logging
import os
import re
import shutil
import subprocess
from typing import Set

import forge.tables as tables
from forge.args import args, command, load_conf
from forge.ccls import write_ccls_file
from forge.colors import Formatter
from forge.conf import Command, Config
from forge.ninjamaker import Environment, create_buildfile
from forge.openocd import create_openocd_file
from forge.peripherals import Clk, cube_peripherals, parse_cube_file
from forge.testing.runner import TestRunner
from forge.ucsim import launch_sim, write_cfg_file

logger = logging.getLogger()


class ForgeError(Exception):
    pass


def get_ninja_env(config: Config) -> Environment | None:
    if not os.path.exists(config.ninja_file):
        return None
    with open(config.ninja_file) as nf:
        header = nf.readline()
        try:
            return Environment(header.replace("# ", "").strip())
        except ValueError:
            return None


def get_sources(src):
    has_main = False
    has_it_c = False
    has_conf_h = False
    sources = []
    for file in os.listdir(src):
        if file == "stm8s_conf.h":
            has_conf_h = True
        if file.endswith(".c"):
            if file == "main.c":
                has_main = True
            if file == "stm8s_it.c":
                has_it_c = True
            sources.append(os.path.join(src, file))
    if not has_main:
        raise ForgeError(f"No main.c file was found in {src}")
    if not has_it_c:
        logger.warning(f"No stm8s_it.c file was found in {src}")
    if not has_conf_h:
        logger.warning(f"No stm8s_conf.h file was found in {src}")

    return sources


def get_flash_model(mcu):
    mcu = mcu.lower()
    matches = []
    for flash_model in tables.stm8flash_suported_models:
        model_re = re.compile(flash_model.lower().replace("?", "\\w?"))
        if model_re.match(mcu) or flash_model.startswith(mcu):
            matches += [flash_model]
    if len(matches) == 0:
        raise ForgeError(f"Can't find a neat flasher config for {mcu}")
    elif len(matches) > 1:
        logger.warning(f"{mcu} matches {matches} flash configurations. Picking one")

    return matches[0]


def swallow(exceptions, fn):
    def wrap(*args, **kwargs):
        try:
            fn(*args, **kwargs)

        except Exception as e:
            for excemption in exceptions:
                if isinstance(e, excemption):
                    return
            raise e

    return wrap


def find_compatible_mcu(mcu):
    matching_mcu = None
    for model in tables.supported_mcus:
        if mcu.startswith(model.lower()):
            matching_mcu = model
            break

    if mcu is not None and matching_mcu is None:
        raise ForgeError(
            f"Cube report specified {mcu} as the MCU model "
            + "and we can't dealwith that"
        )
    return matching_mcu


def add_ignores(config: Config):

    silly_files = set(config.ignore_list())

    lines = set()

    try:
        with open(".gitignore", "r") as f:
            lines = set(f.read().split("\n"))

        ignore_us = silly_files - lines

        with open(".gitignore", "a") as f:
            for mjau in ignore_us:
                f.write(f"{mjau}\n")
    except FileNotFoundError:
        pass


def forge_project(env: Environment, config: Config):
    logger.info(f"Forging project")
    if os.path.exists(config.ninja_file):
        logger.debug("Doing ninja clean")
        subprocess.run(["ninja", "clean"], stdout=subprocess.DEVNULL)
    swallow([FileNotFoundError], shutil.copy)(
        config.ninja_file, "_" + config.ninja_file
    )

    if env == Environment.SIM and shutil.which("ucsim_stm8") is None:
        logger.error("ucsim_stm8 was not found on this system")
        quit(1)

    if shutil.which("ninja") is None:
        logger.error("ninja was not found on this system")
        quit(1)
    if shutil.which("sdcc") is None:
        logger.error("sdcc was not found on this system")
        quit(1)

    try:
        add_ignores(config)
    except Exception as e:
        logger.warning(f"Failed to update gitignore file: {e}")

    if shutil.which("stm8dce") is None:
        logger.warning("stm8dce was not found on this system.")

    try:
        os.stat(os.path.join(config.std_path, "inc", "stm8s.h"))
    except FileNotFoundError:
        logger.error(
            "Could not find stm8s.h in "
            + f'{os.path.join(config.std_path, "inc")} '
            + "std_path."
        )
        quit(1)

    try:
        if config.cube_file:
            with open(config.cube_file, "r") as cube_file:
                logger.info(
                    f"Resolving peripherals and mcu model from {cube_file.name}"
                )
                [mcu, deps] = parse_cube_file(cube_file)
            if mcu is None:
                raise ForgeError("No MCU model found in cube file")
        else:
            [mcu, deps] = [config.mcu, set()]
        if not config.no_clk:
            deps.add(Clk())
        for dep in config.dependencies:
            deps.add(cube_peripherals[dep])
        dep_paths: Set[str] = set()
        for d in deps:
            dep_paths = dep_paths.union(
                set(
                    map(
                        lambda x: os.path.join(config.std_path, "src", x),
                        d.sources,
                    )
                )
            )
        device = find_compatible_mcu(mcu)
        if device is None:
            raise ForgeError(f"{mcu} is not a suported compiletarget")
        flash_model = get_flash_model(mcu)
        logger.info(f"Compiling as {device}, flashing as {flash_model}")
        create_buildfile(
            env,
            device,
            flash_model,
            config,
            get_sources(config.src),
            peripheral_deps=list(dep_paths),
        )
        logger.info(f"Build config written to ./{config.ninja_file}")
        if config.debug:
            create_openocd_file(mcu)

        if config.make_ccls:
            write_ccls_file(device, config)

        swallow([FileNotFoundError], shutil.rmtree)(config.output_dir)
    except ForgeError as e:
        logger.error(e)
        quit(1)
    except Exception as e:
        swallow([FileNotFoundError], os.replace)(
            "_" + config.ninja_file, config.ninja_file
        )
        logger.error("Unkown error when creating build config")
        raise e
    finally:
        swallow([FileNotFoundError], os.remove)("_" + config.ninja_file)


def check_forge_env(desired: Environment, config: Config):
    current_env = get_ninja_env(config)
    if current_env != desired:
        forge_project(desired, config)


def flash():
    subprocess.run(["ninja", "flash"])


def forge():
    config = load_conf()

    logger.setLevel(config.log_level)

    ch = logging.StreamHandler()
    ch.setLevel(config.log_level)

    ch.setFormatter(Formatter())

    logger.addHandler(ch)

    if config.clean:
        if os.path.exists(config.ninja_file):
            subprocess.run(["ninja", "clean"])
            os.unlink(config.ninja_file)

    match command:
        case Command.CLEAN:
            if os.path.exists(config.ninja_file):
                subprocess.run(["ninja", "clean"])
                current_env = get_ninja_env(config)
                os.unlink(config.ninja_file)
                if current_env:
                    forge_project(current_env, config)
        case Command.TEST:
            check_forge_env(Environment.SIM, config)
            runner = TestRunner(config, selected_files=args.files)
            runner.run_all()
        case Command.FLASH:
            check_forge_env(Environment.FLASH, config)
            flash()
        case Command.SIMULATE:
            check_forge_env(Environment.SIM, config)
            if args.generate_conf:
                write_usim(config)
            else:
                launch_sim(config)
        case _:
            logger.error(f"{command} is not a valid command")
            quit(1)


def write_usim(config: Config):
    try:
        write_cfg_file(args.map, config)
    except Exception as e:
        logger.error(f"Failed to create uCsim config: {e}")
        raise e
