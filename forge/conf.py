import logging
import os
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any, Dict, List

import tomllib

logger = logging.getLogger()


std_path_default = "./STM8S_StdPeriph_Lib/Libraries/STM8S_StdPeriph_Driver/"


@dataclass
class UcsimConfig:
    port: int = 1111
    file: str = ".ucsim_config"
    args: List[str] = field(default_factory=list)
    interactive: bool = False
    no_build: bool = False
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
    forge_location: str = os.path.join(
        os.path.split(os.path.dirname(__file__))[0], "forge"
    )

    def __post_init__(self):
        if (
            self.output_dir.startswith("..")
            or self.output_dir == "."
            or self.output_dir == "./"
        ):
            raise Exception(f"having '{self.output_dir}' as outdir is not a good idea")
        if self.cube_file == None and self.mcu == None:
            raise Exception(f"You must either provide cube_file or the mcu")
        self.std_path = os.path.expanduser(self.std_path)
        self.forge_location = os.path.expanduser(self.forge_location)
        pass

    def ignore_list(self):
        return [
            self.ccls_file,
            self.output_dir,
            self.ninja_file,
            ".ccls-cache/",
            ".ninja_log",
            *self.ucsim.ignore_list(),
        ]

    def clean_list(self):
        return [
            self.output_dir,
            *self.ucsim.clean_list(),
        ]


class Command(StrEnum):
    PROJECT = "project"
    SIMULATE = "simulate"
    TEST = "test"
    FLASH = "flash"
    CLEAN = "clean"


def load_conf(path: str = "./forge_conf.toml") -> Config:
    with open(path, "rb") as f:
        data = tomllib.load(f)
        ucsimConf = UcsimConfig(**data.get("ucsim", {}))
        if "ucsim" in data:
            del data["ucsim"]
        conf = Config(ucsim=ucsimConf, **data)
        return conf
