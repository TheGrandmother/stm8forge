import json
import logging
import os
import random
import re
import subprocess
from typing import Any, Dict, Iterator, List, Tuple, cast

from forge.conf import Config

area_header = re.compile(r"Area\s+Addr.*")
value_header = r"\s+Value\s+Global.*"
delim = r"\s+---.*"


logger = logging.getLogger()


def addr(s):
    # The length of the address must match the decoder exactly
    return format(int(s, 16), "#07x")


def parse_map_file(lines: Iterator[str]):
    area = None
    symbol_map: Dict[str, Dict[str, str]] = {}
    stuff = {}
    try:
        while True:
            line = next(lines)
            if re.match(area_header, line) is not None:
                next(lines)  # delimiter
                bob = re.split(r"\s+", next(lines))
                if bob[0] == "INITIALIZER":
                    stuff["initializer"] = addr(bob[1])
                    stuff["init_size"] = int(bob[2], 16)
                if bob[0] == "INITIALIZED":
                    stuff["initialized"] = addr(bob[1])
                area = bob[0]
            elif area is not None:
                if re.match(r"\s{5}\S", line) is not None:
                    value, name = line.strip().split()[:2]
                    symbol_map[area] = symbol_map.get(area, {}) | {
                        name: addr(value),
                    }

    except StopIteration:
        return symbol_map, stuff


def to_var_assignent(value, name):
    return f"var {name} rom[{value}]\n"


def write_cfg_file(map_path: str, config: Config):
    f = open(map_path)
    mjau, stuff = parse_map_file(
        iter(list(map(lambda x: x.replace("\n", ""), f.readlines())))
    )

    conf_json = {"symbols": {}, **stuff}

    with open(config.ucsim.file, "w") as f:
        skipped_areas = ["."]
        if "_sif" in mjau["DATA"].keys() or "_sif" in mjau["INITIALIZED"].keys():
            sif_addr = mjau["DATA"].get("_sif", mjau["INITIALIZED"].get("_sif", None))
            f.write(f"set hw simif rom {sif_addr}\n")
            f.write(f'set hw simif fin "in_simif"\n')
            f.write(f'set hw simif fout "out_simif"\n')
            conf_json["simif"] = {
                "addr": sif_addr,
                "in": "in_simif",
                "out": "out_simif",
            }

        for area, symbols in mjau.items():
            if area in skipped_areas:
                continue
            for name, value in symbols.items():
                conf_json["symbols"][name] = value
                f.write(to_var_assignent(value, name))
    json.dump(conf_json, open(config.ucsim.file + ".json", "w"), indent=2)


def build_interfaces(interfaces: dict[str, Any]):
    options = []
    for p in interfaces:
        match p:
            case "uart":
                for n, opts in interfaces[p].items():
                    options += f"uart={n}," + ",".join(
                        map(
                            lambda t: (
                                "raw" if t[0] == "raw" and t[1] else f"{t[0]}={t[1]}"
                            ),
                            cast(Dict[str, str], opts).items(),
                        )
                    )

            case _:
                logger.warning(f"Unknown simulator peripheral: {p}")
    return [] if len(options) == 0 else ["-S", "".join(options)]


def get_cpu_setting(config: Config):
    valid_devices = [
        "STM8S903",
        "STM8S003",
        "STM8S005",
        "STM8S007",
        "STM8S103",
        "STM8S105",
        "STM8S207",
        "STM8S208",
        "STM8AF52",
        "STM8AF62_12",
        "STM8AF62_46",
        "STM8L",
        "STM8AL3xE",
        "STM8AL3x8",
        "STM8AL3x346",
        "STM8L051",
        "STM8L052C",
        "STM8L052R",
        "STM8L151x23",
        "STM8L15x46",
        "STM8L15x8",
        "STM8L162",
        "STM8L101",
    ]
    mcu = config.mcu
    if mcu is None:
        logger.warning("To use μCsim features specify the mcu model in forge_conf.toml")
        logger.warning("Defaulting to generic STM8S")
        return "STM8S"
    mcu = mcu.upper()
    if mcu.startswith("STM8S001"):
        logger.debug(
            f"mcu is specified as {mcu} will approximate as STM8S003 for simulator"
        )
        return "STM8S003"
    for thing in valid_devices:
        if mcu.startswith(thing):
            return thing
    logger.error(f"No suitable simulator CPU matches {mcu}")
    quit(1)


def build_ucsim_command(options: List[str], config: Config):
    main = os.path.join(config.output_dir, "main.ihx")
    arg = [
        "ucsim_stm8",
        main,
        "-t",
        get_cpu_setting(config),
        "-C",
        config.ucsim.file,
    ]
    return arg + build_interfaces(config.ucsim.interfaces) + options + config.ucsim.args


def launch_headless(config: Config, build=True) -> Tuple[subprocess.Popen[bytes], int]:
    if build:
        subprocess.run(
            ["ninja", "build", config.ucsim.file],
            stdout=subprocess.DEVNULL,
            check=True,
        )

    port = random.randint(10000, 60000)

    command = build_ucsim_command(["-q", "-P", "-Z", str(port)], config)

    logger.debug(" ".join(command))

    instance = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return instance, port


def launch_sim(config: Config):
    if not config.ucsim.no_build:
        build = subprocess.run(
            ["ninja", "build"],
        )

        if build.returncode != 0:
            logger.error("compilation failed")
            return

    subprocess.run(
        ["ninja", config.ucsim.file],
        check=True,
    )
    args = []
    if not config.ucsim.interactive:
        args += [
            "-Z",
            str(config.ucsim.port),
        ]
    command = build_ucsim_command(args, config)
    logger.debug(" ".join(command))
    try:
        subprocess.run(
            command,
            check=True,
        )
    except KeyboardInterrupt:
        print()
        logger.info("Simulation interrupted")
