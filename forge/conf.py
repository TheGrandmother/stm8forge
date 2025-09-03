import tomllib
from dataclasses import dataclass, field, fields, MISSING
from typing import List
from enum import StrEnum
import argparse
import os
import sys


std_path_default = "./STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


@dataclass
class Config:
    cube_file: str
    dependencies: List[str]
    programmer: str = "stlink"
    std_path: str = os.environ.get("STM8_STDLIB_PATH", std_path_default)
    ninja_file: str = "build.ninja"
    output_dir: str = "./build"
    target: str = "main"
    src: str = "."
    no_dce: bool = False
    no_clk: bool = False
    debug: bool = False
    make_ccls: bool = True
    ccls_file: str = ".ccls"
    ucsim_port: int = 1111
    ucsim_file: str = ".ucsim_config"
    ucsim_args: List[str] = field(default_factory=list)
    test_functions_file: str = ".test_functions"
    forge_location: str = os.path.split(os.path.dirname(__file__))[0]

    def __post_init__(self):
        if (
            self.output_dir.startswith("..")
            or self.output_dir == "."
            or self.output_dir == "./"
        ):
            raise Exception(
                f"having '{self.output_dir}' as outdir is not a good idea"
            )
        pass

    def ignore_list(self):
        return [
            self.output_dir,
            self.ninja_file,
            self.ucsim_file,
            self.ucsim_file + ".json",
            self.test_functions_file,
            self.ccls_file,
            "*_simif",
            "*_simif",
            ".ccls-cache/",
            ".ninja_log",
        ]

    def clean_list(self):
        return [
            self.output_dir,
            self.ucsim_file,
            self.test_functions_file,
        ]


defaults = {
    field.name: field.default
    for field in fields(Config)
    if field.default is not MISSING
}


main_parser = argparse.ArgumentParser(
    prog="forge",
    description="Generates build files and stuff for SDCC based STM8 projects",
)

subparsers = main_parser.add_subparsers(help="subcommand help")

ucsim_parser = subparsers.add_parser(
    "simulate",
    help="simulates the project using μCsim",
)

# Generate uccssim configuration.
ucsim_parser.add_argument(
    "--generate-conf",
    dest="generate_conf",
    action="store_true",
    help=argparse.SUPPRESS,
)


# Map for sim generation.
ucsim_parser.add_argument(
    "--map",
    type=str,
    help=argparse.SUPPRESS,
)

ucsim_parser.add_argument(
    "--start",
    dest="start",
    action="store_true",
    help="Start the simulation",
)


parser = subparsers.add_parser(
    "project",
    help="Forges the project in accordance with the decrees of the configuration",
)

parser.add_argument(
    "--debug",
    metavar="d",
    action="store_const",
    const=True,
    default=defaults["debug"],
    help="Build with dbg stuff",
)

parser.add_argument(
    "--no-clk",
    dest="no_clk",
    action="store_const",
    const=True,
    default=defaults["no_clk"],
    help="disables inclusion of the CLK peripheral by default",
)

parser.add_argument(
    "--programmer",
    dest="programmer",
    metavar="programmer",
    default=defaults["programmer"],
    help="What st programmer to use",
)

parser.add_argument(
    "--no-dce",
    dest="no_dce",
    action="store_true",
    help="Disables dead code elimination",
    default=defaults["no_dce"],
)

test_parser = subparsers.add_parser(
    "test",
    help="launches the forge test framework",
)


test_parser.add_argument(
    "--resolve",
    dest="processed_files",
    type=str,
    nargs="+",
    help=argparse.SUPPRESS,
)


if len(sys.argv) == 1:
    print(main_parser.format_help())
    quit(1)


class Command(StrEnum):
    PROJECT = "project"
    SIMULATE = "simulate"
    TEST = "test"


if "--" in sys.argv:
    tail_args = sys.argv[sys.argv.index("--") + 1 :]
    command_args = sys.argv[: sys.argv.index("--")]
else:
    command_args = sys.argv
    tail_args = []

args = main_parser.parse_args(command_args[1:])
command = Command(sys.argv[1])


def load_conf(path: str = "./forge_conf.toml"):
    with open(path, "rb") as f:
        data = tomllib.load(f)
        conf = Config(**data)
        if command == Command.PROJECT:
            conf.no_dce = args.no_dce
            conf.no_clk = args.no_clk
            conf.debug = args.debug
            conf.programmer = args.programmer
        if command == Command.SIMULATE:
            if args.start:
                conf.ucsim_args += ["-g"]
            conf.ucsim_args += tail_args
        return conf
