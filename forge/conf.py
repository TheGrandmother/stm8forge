import tomllib
from dataclasses import dataclass
from typing import List
import argparse
import os


std_path_default = "./STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


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
    # action="store",
    help="Path to STM8CubeMX .txt report file",
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
    "--std",
    dest="std_path",
    metavar="stp path",
    action="store",
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
    "--dependencies",
    dest="dependencies",
    metavar="i",
    default="",
    help="Specify dependencies, comma separated list",
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

args = parser.parse_args()


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
        return Config(
            cube_file=data.get("cube_file", args.cube_file),
            programmer=data.get("programmer", args.programmer),
            std_path=data.get("std_path", args.std_path),
            dependencies=data.get(
                "dependencies",
                map(lambda x: x.upper(), args.dependencies.split(",")),
            ),
            no_clk=data.get("no_clk", args.no_clk),
            no_dce=data.get("no_dce", args.no_dce),
            src=data.get("src", args.src),
        )
