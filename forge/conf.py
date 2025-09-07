import logging
import tomllib
from dataclasses import dataclass, field
from typing import List, Dict, Any
from enum import StrEnum
import argparse
import os
import sys


logger = logging.getLogger()


std_path_default = "./STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


@dataclass
class UcsimConfig:
    port: int = 1111
    file: str = ".ucsim_config"
    args: List[str] = field(default_factory=list)
    interactive: bool = False
    interfaces: Dict[str, Any] = field(default_factory=dict)

    def ignore_list(self):
        return [
            self.file,
            self.file + ".json",
            "*_simif",
        ]

    def clean_list(self):
        return [
            "*_simif",
        ]


@dataclass
class Config:
    ucsim: UcsimConfig
    log_level: int = logging.INFO
    cube_file: str | None = None
    mcu: str | None = None
    dependencies: List[str] = field(default_factory=list)
    programmer: str = "stlink"
    std_path: str = os.environ.get("STM8_STDLIB_PATH", std_path_default)
    ninja_file: str = "build.ninja"
    output_dir: str = "./build"
    target: str = "main"
    src: str = "."
    no_clk: bool = False
    debug: bool = False
    make_ccls: bool = True
    ccls_file: str = ".ccls"
    clean: bool = False
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
        if self.cube_file == None and self.mcu == None:
            raise Exception(f"You must either provide cube_file or the mcu")
        self.std_path = os.path.expanduser(self.std_path)
        pass

    def ignore_list(self):
        return [
            self.test_functions_file,
            self.ccls_file,
            ".ccls-cache/",
            ".ninja_log",
            *self.ucsim.ignore_list(),
        ]

    def clean_list(self):
        return [
            self.output_dir,
            self.test_functions_file,
            *self.ucsim.clean_list(),
        ]


class Command(StrEnum):
    PROJECT = "project"
    SIMULATE = "simulate"
    TEST = "test"
    FLASH = "flash"


main_parser = argparse.ArgumentParser(
    prog="forge",
    description="Generates build files and stuff for SDCC based STM8 projects",
)

subparsers = main_parser.add_subparsers(help="subcommand help")

ucsim_parser = subparsers.add_parser(
    "simulate",
    help="simulates the project using μCsim",
)

flash_parser = subparsers.add_parser(
    "flash",
    help="Flash the microcontroller",
)

flash_parser.add_argument(
    "--clean",
    dest="clean",
    action="store_true",
    help="Clean before building",
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
    help="Start execution (main) directly.",
)

ucsim_parser.add_argument(
    "-i",
    dest="interactive",
    action="store_true",
    help="Run the simulator in interactive mode",
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
    help="Build with dbg stuff",
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


if "--" in sys.argv:
    tail_args = sys.argv[sys.argv.index("--") + 1 :]
    command_args = sys.argv[: sys.argv.index("--")]
else:
    command_args = sys.argv
    tail_args = []

args = main_parser.parse_args(command_args[1:])

# this is horrible
command = Command(sys.argv[1])


def override(target: object, option: str):
    if args.__getattribute__(option) is not None:
        target.__setattr__(option, args.__getattribute__(option))


def load_conf(path: str = "./forge_conf.toml"):
    try:
        with open(path, "rb") as f:
            data = tomllib.load(f)
            ucsimConf = UcsimConfig(**data.get("ucsim", {}))
            if command == Command.SIMULATE:
                if args.start is not None:
                    ucsimConf.args += ["-g"]
                ucsimConf.args += tail_args
                ucsimConf.interactive = args.interactive
                override(ucsimConf, "interactive")
            if "ucsim" in data:
                del data["ucsim"]
            conf = Config(ucsim=ucsimConf, **data)
            if command == Command.PROJECT:
                override(conf, "debug")
            if command == Command.FLASH:
                override(conf, "clean")
            return conf
    except FileNotFoundError:
        logger.error("No forge_conf.toml file found.")
        quit(1)
