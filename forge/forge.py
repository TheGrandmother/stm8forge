#!/bin/python3
import argparse
import os
import sys
import shutil
import re


import forge.ninja as ninja
import forge.colors as colors
import forge.tables as tables
from forge.openocd import create_openocd_file
from forge.ninjamaker import create_buildfile
from forge.peripherals import parse_cube_file, Clk, cube_peripherals

parser = argparse.ArgumentParser(
    prog="forge",
    description="Generates build files and stuff for SDCC based STM8 projects",
)

parser.add_argument(
    "--cube-file",
    metavar="cf",
    dest="cube_file",
    type=str,
    default=None,
    action="store",
    help="Path to STM8CubeMX .txt report file",
)

parser.add_argument(
    "--debug",
    metavar="d",
    const="--debug",
    action="store_const",
    default="",
    help="Build with dbg stuff",
)

parser.add_argument(
    "--stdp",
    dest="stdp_path",
    metavar="stpd path",
    action="store",
    default=".",
    help="Path to the STM8S_StdPeriph_Lib. defaults to `.`",
)

parser.add_argument(
    "--src",
    dest="src",
    metavar="src",
    action="store",
    default=".",
    help="Location of project source files, defaults to `.`",
)

parser.add_argument(
    "--no-clk",
    dest="no_clk",
    action="store_const",
    const=True,
    default=False,
    help="disables inclusion of the CLK peripheral by default",
)

parser.add_argument(
    "--includes",
    dest="includes",
    metavar="i",
    default=None,
    help="Specify dependencies, comma separated list",
)


args = parser.parse_args()


ninja_file = "build.ninja"
output_dir = "./build"

lib_to_driver = "STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


class ForgeError(Exception):
    pass


def get_sources():
    has_main = False
    has_it_c = False
    has_conf_h = False
    sources = []
    for file in os.listdir(args.src):
        if file == "stm8s_conf.h":
            has_conf_h = True
        if file.endswith(".c"):
            if file == "main.c":
                has_main = True
                continue
            if file == "stm8s_it.c":
                has_it_c = True
            sources.append(os.path.join(args.src, file))
    if not has_main:
        raise ForgeError(f"No main.c file was found in {args.src}")
    if not has_it_c:
        colors.warning(f"No stm8s_it.c file was found in {args.src}")
    if not has_conf_h:
        colors.warning(f"No stm8s_conf.h file was found in {args.src}")

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
    swallow([FileNotFoundError], os.replace)(ninja_file, "_" + ninja_file)
    if shutil.which("ninja") is None:
        colors.error("ninja was not found on this system")
        quit(1)
    try:
        os.stat(os.path.join(args.stdp_path, lib_to_driver, "inc", "stm8s.h"))
    except FileNotFoundError:
        colors.error(
            "Could not find stm8s.h in "
            + f'{os.path.join(args.stdp_path, lib_to_driver, "inc")} '
            + "forge is kinda certain that --stdp_path is wrong."
        )
        quit(1)

    try:
        if args.cube_file is None:
            colors.error("No cube file specified")
            exit(1)
        with open(args.cube_file, "r") as cube_file:
            colors.success(
                f"Resolving peripherals and mcu model from {cube_file.name}"
            )
            [mcu, deps] = parse_cube_file(cube_file)
            if not args.no_clk:
                deps.add(Clk())
            if args.includes is not None:
                for dep in map(lambda x: x.upper(), args.includes.split(",")):
                    deps.add(cube_peripherals[dep])
            if mcu is None:
                raise ForgeError("No MCU model found in cube file")
            dep_paths = []
            for d in deps:
                dep_paths = dep_paths + list(
                    map(
                        lambda x: os.path.join(
                            args.stdp_path, lib_to_driver, "src", x
                        ),
                        d.sources,
                    )
                )
            device = find_compatible_mcu(mcu)
            flash_model = get_flash_model(mcu)
            colors.success(f"Compiling as {device}, flashing as {flash_model}")
            create_buildfile(
                device,
                flash_model,
                args.stdp_path,
                args.debug,
                get_sources(),
                peripheral_deps=dep_paths,
            )
            colors.success(f"Build config written to ./{ninja_file}")
            if args.debug:
                create_openocd_file(mcu)

            swallow([FileNotFoundError], shutil.rmtree)("build/")
            quit(0)
    except ForgeError as e:
        colors.error(e)
        quit(1)
    except Exception as e:
        swallow([FileNotFoundError], os.replace)("_" + ninja_file, ninja_file)
        colors.error("Unkown error when creating build config:")
        raise e
    finally:
        swallow([FileNotFoundError], os.remove)("_" + ninja_file)
