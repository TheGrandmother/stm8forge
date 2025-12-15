import argparse
import logging
import sys

import tomllib

from forge.conf import Command, Config, UcsimConfig

logger = logging.getLogger()

main_parser = argparse.ArgumentParser(
    prog="forge",
    description="Generates build files and stuff for SDCC based STM8 projects",
)

main_parser.add_argument(
    "--verbose",
    action="store_const",
    dest="log_level",
    const=0,
    help="Debug output",
)

main_parser.add_argument(
    "--clean",
    dest="clean",
    action="store_true",
    help="Clean before command",
)


subparsers = main_parser.add_subparsers(help="subcommand help")

subparsers.add_parser(
    "clean",
    help="clean project",
)

ucsim_parser = subparsers.add_parser(
    "simulate",
    help="simulates the project using μCsim",
)

flash_parser = subparsers.add_parser(
    "flash",
    help="Flash the microcontroller",
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


# Map for sim generation.
ucsim_parser.add_argument(
    "--no-build",
    dest="no_build",
    action="store_true",
    help="Omitts building",
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
    dest="files",
    type=str,
    nargs="+",
    help=argparse.SUPPRESS,
)


test_parser.add_argument(
    "files",
    type=str,
    nargs="*",
    help="Files to be tested, if omitted all *_test.c files will be ran",
)


def override(target: object, option: str):
    try:
        if args.__getattribute__(option) is not None:
            target.__setattr__(option, args.__getattribute__(option))
    except AttributeError:
        pass


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
command = Command(list(filter(lambda x: not x.startswith("-"), sys.argv[1:]))[0])


def load_conf(path: str = "./forge_conf.toml") -> Config:
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
            if command == Command.TEST:
                override(conf, "debug")
            override(conf, "clean")
            override(conf, "log_level")
            return conf
    except FileNotFoundError:
        logger.error("No forge_conf.toml file found.")
        quit(1)
