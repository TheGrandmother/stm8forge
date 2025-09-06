import re
from typing import Dict, Iterator, Any, cast
import subprocess

from forge.conf import Config
import os
import json
import logging

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
        if (
            "_sif" in mjau["DATA"].keys()
            or "_sif" in mjau["INITIALIZED"].keys()
        ):
            sif_addr = mjau["DATA"].get(
                "_sif", mjau["INITIALIZED"].get("_sif", None)
            )
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
                                "raw"
                                if t[0] == "raw" and t[1]
                                else f"{t[0]}={t[1]}"
                            ),
                            cast(Dict[str, str], opts).items(),
                        )
                    )

            case _:
                logger.warning(f"Unknown simulator peripheral: {p}")
    return [] if len(options) == 0 else ["-S", "".join(options)]


def launch_sim(config: Config):
    main = os.path.join(config.output_dir, "main.ihx")
    build = subprocess.run(
        ["ninja", main],
    )

    if build.returncode != 0:
        logger.error("compilation failed")
        return

    subprocess.run(
        ["ninja", config.ucsim.file],
        check=True,
    )
    arg = [
        "ucsim_stm8",
        main,
        "-t",
        "STM8S",
        "-C",
        config.ucsim.file,
    ]
    if not config.ucsim.interactive:
        arg += [
            "-Z",
            str(config.ucsim.port),
        ]
    arg += config.ucsim.args
    arg += build_interfaces(config.ucsim.interfaces)
    logger.debug(" ".join(arg))
    try:
        subprocess.run(
            arg,
            check=True,
        )
    except KeyboardInterrupt:
        print()
        logger.info("Simulation interrupted")
