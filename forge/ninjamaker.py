import os
import sys
import subprocess


import forge.ninja as ninja
import forge.colors as colors
from forge.conf import Config


ninja_file = "build.ninja"
output_dir = "./build"

stm8_lib_path = "/usr/local/share/sdcc/lib/stm8/stm8.lib"


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
    + "--no-peep --all-callee-saves --opt-code-size"
)


def create_buildfile(
    device: str,
    flash_model: str,
    config: Config,
    sources: list[str],
    use_dce=True,
    peripheral_deps=[],
):
    with open(ninja_file, "w") as f:
        sources = sources + peripheral_deps + ["./main.c"]
        w = ninja.Writer(f)
        w.variable("device", device)
        w.variable("outdir", output_dir)
        w.variable("flash_model", flash_model)
        w.variable(
            "includes",
            "-I./ " + "-I" + os.path.join(config.std_path, "inc"),
        )

        w.variable(
            "compile_directives",
            standard_flags,
        )

        ihx_output = os.path.join(output_dir, "main.ihx")
        elf_output = os.path.join(output_dir, "main.elf")

        w.variable(
            "cflags",
            "-mstm8 --std-sdcc99 -D $device $compile_directives",
        )

        w.newline()
        w.rule("dep", "sdcc $cflags $includes -o $outdir/ -c $in")
        w.rule("main", "sdcc $cflags $includes -o $outdir/ $in")
        w.rule("compile_asm", "sdcc $cflags $includes -S -o $out $in")
        w.rule("assemble", "sdasstm8 -plosg -ff -o $out $in")
        w.rule(
            "debug",
            "sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/ $in",
        )

        if use_dce:
            w.rule(
                "dce",
                f"stm8dce -o $outdir/smol {stm8_lib_path} $in && touch $outdir/.smollified",
            )
        else:
            w.rule(
                "dce",
                f"cp $outdir/asm/* $outdir/smol/ && touch $outdir/.smollified",
            )

        w.rule(
            "link",
            f"sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/main.elf $in",
        )

        w.rule(
            "ihx",
            f"stm8-objcopy --remove-section='.debug*' --remove-section=SSEG --remove-section=INITIALIZED --remove-section=DATA $in -O ihex $out",
        )

        flash_cmd = f"stm8flash -c {config.programmer} -p $flash_model -w $in && touch .flash_dummy"

        w.rule("write_to_flash", flash_cmd)

        w.rule("_reforge", " ".join(sys.argv))

        w.rule("_clean", "rm -r $outdir")
        w.rule(
            "_dirs",
            "mkdir -p $outdir && mkdir -p $outdir/obj && mkdir -p $outdir/smol && mkdir -p $outdir/asm",
        )

        if config.debug:
            w.rule("_listen", "./serve_openocd")

        w.newline()
        w.comment("actions")
        w.build(
            ".flash_dummy",
            "write_to_flash",
            [ihx_output],
        )
        w.build(
            "flash",
            "phony",
            ["dirs", ninja_file, ihx_output, ".flash_dummy"],
        )
        w.build(
            "build",
            "phony",
            ["dirs", ninja_file, ihx_output],
        )
        w.build(
            "debug",
            "phony",
            ["dirs", ninja_file, elf_output],
        )
        w.build(
            "clean",
            "_clean",
            [],
        )

        w.build(
            "reforge",
            "_reforge",
            [],
        )
        w.build(
            "dirs",
            "_dirs",
            [],
        )

        w.newline()
        w.comment("targets")

        w.newline()
        w.comment("asm_targets")
        for dep in sources:
            w.build(make_target(dep, ".asm", "asm"), "compile_asm", [dep])

        w.newline()
        w.comment("smol_asm")
        w.build(
            "$outdir/.smollified",
            "dce",
            [make_target(dep, ".asm", "asm") for dep in sources],
        )
        w.newline()
        for dep in sources:
            w.build(
                make_target(dep, ".asm", "smol"),
                "phony",
                ["$outdir/.smollified", make_target(dep, ".asm", "asm")],
            )

        w.newline()
        w.comment("obj_targets")
        for dep in sources:
            w.build(
                make_target(dep, ".rel", "obj"),
                "assemble",
                [make_target(dep, ".asm", "smol")],
            )

        w.newline()
        w.comment("linkidink")
        w.build(
            "build/main.elf",
            "link",
            [make_target(dep, ".rel", "obj") for dep in sources],
        )

        w.newline()
        w.comment("ihx")
        w.build(
            "build/main.ihx",
            "ihx",
            ["build/main.elf"],
        )
