import os
import sys


import forge.ninja as ninja
from forge.conf import Config
from forge.testing.test_setup import show_func_defs


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
    + "--no-peep --all-callee-saves --opt-code-size "
    + "--disable-warning 283"
)


def find_test_funcitons(sources):
    for source in sources:
        show_func_defs(make_target(source, ".c", "pre"))


def create_buildfile(
    device: str,
    flash_model: str,
    config: Config,
    sources: list[str],
    use_dce=True,
    peripheral_deps=[],
):
    def target(ending):
        return os.path.join(config.output_dir, f"{config.target}.{ending}")

    with open(ninja_file, "w") as f:
        sources = sources + peripheral_deps + [f"./{config.target}.c"]
        w = ninja.Writer(f)
        w.variable("forge_command", sys.argv[0])
        w.variable("device", device)
        w.variable("outdir", output_dir)
        w.variable("flash_model", flash_model)
        w.variable("lib_path", stm8_lib_path)
        includes = "-I./ " + "-I" + os.path.join(config.std_path, "inc")
        w.variable(
            "includes",
            includes,
        )

        w.variable(
            "compile_directives",
            standard_flags,
        )

        ihx_target = target("ihx")
        elf_target = target("elf")

        w.variable(
            "cflags",
            "-mstm8 --std-sdcc99 -D $device $compile_directives",
        )

        w.newline()
        w.rule("dep", "sdcc $cflags $includes -o $outdir/ -c $in")
        w.rule("main", "sdcc $cflags $includes -o $outdir/ $in")
        w.rule("compile_asm", "sdcc $cflags $includes -S -o $out $in")

        w.rule("pre_process", "sdcc $cflags $includes -E -o $out $in")

        w.rule("assemble", "sdasstm8 -plosg -ff -o $out $in")
        w.rule(
            "debug",
            "sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/ $in",
        )

        w.rule(
            "resolve_test_functions",
            "$forge_command test --resolve $in",
        )

        if use_dce:
            w.rule(
                "dce",
                "mkdir -p $outdir/smol && "
                + f"xargs < {config.test_functions_file} stm8dce -o $outdir/smol $lib_path $in && "
                + "touch $outdir/.smollified",
            )
        else:
            w.rule(
                "dce",
                "mkdir -p $outdir/smol && cp $outdir/asm/* $outdir/smol/ && touch $outdir/.smollified",
            )

        w.rule(
            "link",
            f"sdcc $cflags --debug --out-fmt-elf $includes -o $outdir/main.elf $in",
        )

        w.rule(
            "ihx",
            f"stm8-objcopy --remove-section='.debug*' --remove-section=SSEG --remove-section=INITIALIZED --remove-section=DATA $in -O ihex $out",
        )

        flash_cmd = f"stm8flash -c {config.programmer} -p $flash_model -w $in"

        w.rule("write_to_flash", flash_cmd)

        w.rule("_reforge", " ".join(sys.argv))

        w.rule(
            "_make_ucsim_config",
            f"$forge_command simulate --generate-conf --map $in",
        )

        w.rule(
            f"_clean",
            f"(rm -r {' '.join(config.clean_list())} 2> /dev/null) || true",
        )

        w.rule(
            "_dirs",
            "mkdir -p $outdir && mkdir -p $outdir/obj && mkdir -p $outdir/smol && mkdir -p $outdir/asm",
        )

        if config.debug:
            w.rule("_listen", "./serve_openocd")

        w.newline()
        w.comment("actions")
        w.build(
            "_flash",
            "write_to_flash",
            [ihx_target],
        )
        w.build(
            "flash",
            "phony",
            ["dirs", ninja_file, ihx_target, "_flash"],
        )
        w.build(
            "build",
            "phony",
            ["dirs", ninja_file, ihx_target],
        )
        w.build(
            "debug",
            "phony",
            ["dirs", ninja_file, ihx_target],
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
        w.comment("test")
        w.build(
            ".test_functions",
            "resolve_test_functions",
            [make_target(dep, ".c", "pre") for dep in sources],
        )

        w.build(
            "test_setup",
            "phony",
            [
                config.test_functions_file,
                config.ucsim_file,
                ihx_target,
            ],
        )

        w.newline()
        w.comment("Pre process files")
        for dep in sources:
            w.build(make_target(dep, ".c", "pre"), "pre_process", [dep])

        w.newline()
        w.comment("asm_targets")
        for dep in sources:
            w.build(make_target(dep, ".asm", "asm"), "compile_asm", [dep])

        w.newline()
        w.comment("smol_asm")
        w.build(
            "$outdir/.smollified",
            "dce",
            [".test_functions"]
            + [make_target(dep, ".asm", "asm") for dep in sources],
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

        w.newline()
        w.comment("uCsim configuration file")
        w.build(
            config.ucsim_file,
            "_make_ucsim_config",
            [
                target("map"),
            ],
        )
