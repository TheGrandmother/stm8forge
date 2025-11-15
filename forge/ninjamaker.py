import os
import sys

import logging


from enum import StrEnum
import forge.ninja as ninja
from forge.conf import Config
from forge.testing.test_setup import show_func_defs

ninja_file = "build.ninja"
output_dir = "./build"

stm8_lib_path = "/usr/local/share/sdcc/lib/stm8/stm8.lib"


logger = logging.getLogger()


def make_target(source, suffix, path=""):
    return os.path.join(
        output_dir, path, source.split("/")[-1].replace(".c", suffix)
    )


def gen_rel_target(dep):
    return os.path.join(output_dir, dep.split("/")[-1].replace(".c", ".rel"))


def gen_asm_target(dep):
    return os.path.join(output_dir, dep.split("/")[-1].replace(".c", ".asm"))


def gen_smol_asm_target(dep):
    return os.path.join(
        output_dir, "smol", dep.split("/")[-1].replace(".c", ".asm")
    )


standard_flags = (
    "--stack-auto --fverbose-asm --float-reent "
    + "--no-peep --all-callee-saves --opt-code-size "
    + "--disable-warning 283"
)


def find_test_funcitons(sources):
    for source in sources:
        show_func_defs(make_target(source, ".c", "pre"))


class Environment(StrEnum):
    DEBUG = "DEBUG"
    SIM = "SIM"
    FLASH = "FLASH"


def create_buildfile(
    env: Environment,
    device: str,
    flash_model: str,
    config: Config,
    sources: list[str],
    peripheral_deps: list[str] = [],
):
    def target(ending):
        return os.path.join(config.output_dir, f"{config.target}.{ending}")

    with open(ninja_file, "w") as f:
        sources = sources + peripheral_deps
        forge_lib = os.path.join(config.forge_location, "lib")

        sources = sources + list(
            map(
                lambda x: os.path.join(forge_lib, x),
                filter(lambda x: x.endswith(".c"), os.listdir(forge_lib)),
            )
        )

        test_files = list(
            filter(
                lambda s: os.path.basename(s).endswith("_test.c"),
                sources,
            )
        )

        if not env == Environment.SIM:
            if len(test_files) > 0:
                logger.info(f"Ignoring {len(test_files)} *_test.c files")
                sources = list(set(sources) - set(test_files))

        w = ninja.Writer(f)
        w.comment(env)

        w.variable("device", device)
        w.variable("forge_command", sys.argv[0])
        w.variable(
            "defines",
            " -D".join(
                ["", device, *(["UCSIM"] if env == Environment.SIM else [])]
            ),
        )

        w.variable("outdir", output_dir)
        w.variable("flash_model", flash_model)
        w.variable("lib_path", stm8_lib_path)
        w.variable(
            "includes",
            " -I".join(
                [
                    "",
                    config.src,
                    os.path.join(config.std_path, "inc"),
                    forge_lib,
                ]
            ),
        )

        w.variable(
            "compile_directives",
            standard_flags,
        )

        w.variable(
            "copy_flags",
            "--remove-section='.debug*' --remove-section=SSEG --remove-section=INITIALIZED --remove-section=DATA",
        )

        ihx_target = target("ihx")
        elf_target = target("elf")

        w.variable(
            "cflags",
            "-mstm8 --std-sdcc99 $defines $compile_directives",
        )

        w.newline()
        w.comment("Standard rules")

        w.rule("main", "sdcc $cflags $includes -o $outdir/ $in")
        w.rule(
            "debug",
            "sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/ $in",
        )
        w.rule("dep", "sdcc $cflags $includes -o $outdir/ -c $in")
        w.rule("compile_asm", "sdcc $cflags $includes -S -o $out $in")
        w.rule("pre_process", "sdcc $cflags $includes -E -o $out $in")
        w.rule("assemble", "sdasstm8 -plosg -ff -o $out $in")
        w.rule(
            "link",
            f"sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/main.elf $in",
        )
        w.rule(
            "ihx",
            "stm8-objcopy $copy_flags $in -O ihex $out",
        )
        w.rule(
            "dce",
            "mkdir -p $outdir/smol && "
            + f"stm8dce -xf $${{DCE_EXCLUDES:='_'}} -o $outdir/smol $lib_path $in && "
            + "touch $outdir/.smollified",
        )
        w.rule(
            "_dirs",
            "mkdir -p $outdir && mkdir -p $outdir/obj && mkdir -p $outdir/smol && mkdir -p $outdir/asm",
        )
        w.rule(
            f"_clean",
            f"(rm -r {' '.join(config.clean_list())} 2> /dev/null) || true",
        )

        if env == Environment.FLASH:
            w.newline()
            w.comment("Flash rules")
            w.rule(
                "write_to_flash",
                f"stm8flash -c {config.programmer} -p $flash_model -w $in",
            )

        if env == Environment.DEBUG:
            w.newline()
            w.comment("Debug rules")
            w.rule(
                "debug",
                "sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/ $in",
            )
            w.rule("_listen", "./serve_openocd")

        if env == Environment.SIM:
            w.newline()
            w.comment("Simulator rules")
            w.rule(
                "resolve_test_functions",
                "$forge_command test --resolve $in",
            )

            w.rule(
                "_make_ucsim_config",
                f"$forge_command simulate --generate-conf --map $in",
            )

        w.newline()
        w.comment("Standard targets")
        w.build(
            "dirs",
            "_dirs",
            [],
        )

        w.build(
            "clean",
            "_clean",
            [],
        )

        w.build(
            "build",
            "phony",
            [ihx_target],
        )

        if env == Environment.FLASH:
            w.newline()
            w.comment("Flash targets")
            w.build(
                "_flash",
                "write_to_flash",
                [ihx_target],
                order_only=["dirs"],
            )
            w.build(
                "flash",
                "phony",
                ["_flash"],
            )

        if env == Environment.DEBUG:
            w.newline()
            w.comment("Debug targets")
            w.build(
                "debug",
                "phony",
                ["dirs", ninja_file, elf_target],
            )

        if env == Environment.SIM:
            w.newline()
            w.comment("Sim targets")
            w.build(
                "pre",
                "phony",
                [make_target(dep, ".c", "pre") for dep in sources],
            )
            w.build(
                config.ucsim.file,
                "_make_ucsim_config",
                [
                    target("map"),
                ],
            )

        w.newline()
        w.newline()
        w.newline()
        w.comment("Dependencies")

        w.comment("Pre process files")
        for dep in sources:
            w.build(make_target(dep, ".c", "pre"), "pre_process", [dep])

        w.newline()
        w.comment("asm_targets")
        for dep in sources:
            w.build(make_target(dep, ".asm", "asm"), "compile_asm", [dep])

        w.newline()
        w.comment("Smallification")
        smalling_sources = (
            set(sources)
            # - set(test_files)
            # - set([os.path.join(forge_lib, "forge.c")])
        )
        non_smalling = []  # test_files + [os.path.join(forge_lib, "forge.c")]

        w.build(
            "smallify",
            "dce",
            [make_target(dep, ".asm", "asm") for dep in smalling_sources],
        )

        w.newline()
        for dep in smalling_sources:
            w.build(
                make_target(dep, ".asm", "smol"),
                "phony",
                [
                    "smallify",
                    make_target(dep, ".asm", "asm"),
                ],
            )

        w.newline()
        for dep in smalling_sources:
            w.build(
                make_target(dep, ".rel", "obj"),
                "assemble",
                [make_target(dep, ".asm", "smol")],
            )

        for dep in non_smalling:
            w.build(
                make_target(dep, ".rel", "obj"),
                "assemble",
                [make_target(dep, ".asm", "asm")],
            )

        w.newline()
        w.comment("linkidink")
        w.build(
            elf_target,
            "link",
            [make_target(dep, ".rel", "obj") for dep in sources],
        )

        w.newline()
        w.comment("map file")
        w.build(
            target("map"),
            "phony",
            [ihx_target, "dirs"],
        )

        w.newline()
        w.comment("ihx")
        w.build(
            ihx_target,
            "ihx",
            [elf_target],
        )
