import tomllib
from dataclasses import dataclass, field
from typing import List
from enum import StrEnum
import argparse
import os
import sys


std_path_default = "./STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


main_parser = argparse.ArgumentParser(
    prog="forge",
    description="Generates build files and stuff for SDCC based STM8 projects",
)

subparsers = main_parser.add_subparsers(help="subcommand help")

ucsim_parser = subparsers.add_parser(
    "simulate",
    help="simulates the project using μCsim",
)

ucsim_parser.add_argument(
    "--generate-conf",
    dest="generate_conf",
    action="store_true",
    help="Generate uccssim configuration.",
)

ucsim_parser.add_argument(
    "--start",
    dest="start",
    action="store_true",
    help="Start the simulation",
)

ucsim_parser.add_argument(
    "--map",
    type=str,
    help="input map file. pointless without --generate-conf",
)


parser = subparsers.add_parser(
    "project",
    help="Forges the project in accordance with the decrees of the configuration",
)

parser.add_argument(
    "--debug",
    metavar="d",
    const="--debug",
    action="store_const",
    # default="",
    help="Build with dbg stuff",
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
    "--programmer",
    dest="programmer",
    metavar="programmer",
    default="stlink",
    help="What st programmer to use",
)

parser.add_argument(
    "--no-dce",
    dest="no_dce",
    action="store_true",
    help="Disables dead code elimination",
)


if len(sys.argv) == 1:
    print(main_parser.format_help())
    quit(1)


class Command(StrEnum):
    PROJECT = "project"
    SIMULATE = "simulate"


if "--" in sys.argv:
    tail_args = sys.argv[sys.argv.index("--") + 1 :]
    command_args = sys.argv[: sys.argv.index("--")]
else:
    command_args = sys.argv
    tail_args = []

args = main_parser.parse_args(command_args[1:])
command = Command(sys.argv[1])


@dataclass
class Config:
    cube_file: str
    dependencies: List[str]
    programmer: str = "stlink"
    std_path: str = os.environ.get("STM8_STDLIB_PATH", std_path_default)
    ninja_file: str = "build.ninja"
    output_dir: str = "./build"
    src: str = "."
    no_dce: bool = False
    no_clk: bool = False
    debug: bool = False
    make_ccls: bool = True
    ucsim_port: int = 1111
    ucsim_config: str = ".ucsim_config"
    ucsim_args: List[str] = field(default_factory=list)

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
