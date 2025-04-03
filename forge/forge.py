#!/bin/python3
import os
import shutil
import re


import forge.colors as colors
import forge.tables as tables
from forge.openocd import create_openocd_file
from forge.conf import load_conf
from forge.ninjamaker import create_buildfile
from forge.peripherals import parse_cube_file, Clk, cube_peripherals
from forge.ccls import write_ccls_file


class ForgeError(Exception):
    pass


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
                continue
            if file == "stm8s_it.c":
                has_it_c = True
            sources.append(os.path.join(src, file))
    if not has_main:
        raise ForgeError(f"No main.c file was found in {src}")
    if not has_it_c:
        colors.warning(f"No stm8s_it.c file was found in {src}")
    if not has_conf_h:
        colors.warning(f"No stm8s_conf.h file was found in {src}")

    return sources


def get_flash_model(mcu):
    mcu = mcu.lower()
    match = None
    for flash_model in tables.stm8flash_suported_models:
        model_re = re.compile(flash_model.replace("?", "\\w?"))
        if model_re.match(mcu):
            if match is None:
                match = flash_model
            else:
                colors.warning(
                    f"{match} and {flash_model} are matching flash configs"
                )
    if match is None:
        raise ForgeError(f"Can't find a neat flasher config for {mcu}")

    return match


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
    for model in tables.stdp_supported_models:
        if mcu.startswith(model):
            matching_mcu = model
            break

    if mcu is not None and matching_mcu is None:
        raise ForgeError(
            f"Cube report specified {mcu} as the MCU model "
            + "and we can't dealwith that"
        )
    return matching_mcu


def forge():
    config = load_conf()
    swallow([FileNotFoundError], os.replace)(
        config.ninja_file, "_" + config.ninja_file
    )
    if shutil.which("ninja") is None:
        colors.error("ninja was not found on this system")
        quit(1)
    if shutil.which("sdcc") is None:
        colors.error("sdcc was not found on this system")
        quit(1)
    use_dce = not config.no_dce
    if shutil.which("stm8dce") is None and not config.no_dce:
        colors.warning(
            "stm8dce was not found on this system. DCE not avaliable, you shoud address this."
        )
        use_dce = False
    if config.no_dce:
        colors.warning("Dce is disabled.")

    try:
        os.stat(os.path.join(config.std_path, "inc", "stm8s.h"))
    except FileNotFoundError:
        colors.error(
            "Could not find stm8s.h in "
            + f'{os.path.join(config.std_path, "inc")} '
            + "std_path."
        )
        quit(1)

    try:
        if config.cube_file is None:
            colors.error("No cube file specified")
            exit(1)
        with open(config.cube_file, "r") as cube_file:
            colors.success(
                f"Resolving peripherals and mcu model from {cube_file.name}"
            )
            [mcu, deps] = parse_cube_file(cube_file)
            if not config.no_clk:
                deps.add(Clk())
            for dep in config.dependencies:
                deps.add(cube_peripherals[dep])
            if mcu is None:
                raise ForgeError("No MCU model found in cube file")
            dep_paths = []
            for d in deps:
                dep_paths = dep_paths + list(
                    map(
                        lambda x: os.path.join(config.std_path, "src", x),
                        d.sources,
                    )
                )
            device = find_compatible_mcu(mcu)
            if device is None:
                raise ForgeError(f"{mcu} is not a suported compiletarget")
            flash_model = get_flash_model(mcu)
            colors.success(f"Compiling as {device}, flashing as {flash_model}")
            create_buildfile(
                device,
                flash_model,
                config,
                get_sources(config.src),
                use_dce=use_dce,
                peripheral_deps=dep_paths,
            )
            colors.success(f"Build config written to ./{config.ninja_file}")
            if config.debug:
                create_openocd_file(mcu)

            if config.make_ccls:
                write_ccls_file(device, config)

            swallow([FileNotFoundError], shutil.rmtree)(config.output_dir)
            quit(0)
    except ForgeError as e:
        colors.error(e)
        quit(1)
    except Exception as e:
        swallow([FileNotFoundError], os.replace)(
            "_" + config.ninja_file, config.ninja_file
        )
        colors.error("Unkown error when creating build config:")
        raise e
    finally:
        swallow([FileNotFoundError], os.remove)("_" + config.ninja_file)
