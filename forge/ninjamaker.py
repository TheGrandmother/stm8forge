import argparse
import os
import sys
import shutil
import re


import forge.ninja as ninja
import forge.colors as colors
import forge.tables as tables
from forge.openocd import create_openocd_file
from forge.peripherals import parse_cube_file, Clk, cube_peripherals


ninja_file = "build.ninja"
output_dir = "./build"

lib_to_driver = "STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


def gen_rel_target(dep):
    return os.path.join(
        output_dir, "rel", dep.split("/")[-1].replace(".c", ".rel")
    )


def create_buildfile(
    device,
    flash_model,
    stdp_path,
    debug: bool,
    sources: list[str],
    peripheral_deps=["./stm8s_it.c"],
):
    with open(ninja_file, "w") as f:
        sources = sources + peripheral_deps
        w = ninja.Writer(f)
        w.variable("device", device)
        w.variable("outdir", output_dir)
        w.variable("flash_model", flash_model)
        w.variable(
            "includes",
            "-I./ " + "-I" + os.path.join(stdp_path, lib_to_driver, "inc"),
        )

        w.variable(
            "compile_directives",
            "--stack-auto --fverbose-asm --float-reent "
            + "--no-peep --all-callee-saves --opt-code-size",
        )

        ihx_output = os.path.join(output_dir, "main.ihx")
        elf_output = os.path.join(output_dir, "main.elf")

        if debug:
            w.variable("debug", "--debug --out-fmt-elf")
        else:
            w.variable("debug", "")

        w.variable(
            "cflags",
            "-mstm8 --std-sdcc99 -D $device $compile_directives",
        )

        w.newline()
        w.rule("rel", "sdcc $cflags $includes -o $outdir/rel/ -c $in")
        w.rule("main", "sdcc $cflags $includes -o $outdir/ $in")
        w.rule(
            "debug",
            "sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/ $in",
        )

        flash_cmd = (
            "stm8flash -c stlink -p $flash_model -w $in"
            + " && touch .flash_dummy"
        )

        # if args.debug:
        #     flash_cmd = 'echo "Can\'t flash when built with --debug" && exit 1'

        w.rule("write_to_flash", flash_cmd)

        w.rule("rebuild", " ".join(sys.argv))

        w.rule("_clean", "rm -r $outdir")

        if debug:
            w.rule("_listen", "./serve_openocd")

        w.newline()
        w.build(
            ihx_output,
            "main",
            ["main.c", *[gen_rel_target(dep) for dep in sources]],
        )
        w.build(
            elf_output,
            "debug",
            ["main.c", *[gen_rel_target(dep) for dep in sources]],
        )
        w.build(
            ".flash_dummy",
            "write_to_flash",
            [ihx_output],
        )
        w.build(
            "flash",
            "phony",
            [ninja_file, ihx_output, ".flash_dummy"],
        )
        w.build(
            "build",
            "phony",
            [ninja_file, ihx_output],
        )
        w.build(
            "debug_build",
            "phony",
            [ninja_file, elf_output],
        )
        w.build(
            "clean",
            "_clean",
            [],
        )

        w.build(
            "./build.ninja",
            "rebuild",
            [sys.argv[0]],
        )

        w.newline()
        w.comment("deps")
        for dep in sources:
            w.build(gen_rel_target(dep), "rel", [dep])
