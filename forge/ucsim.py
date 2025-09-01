import re
from typing import Dict, Iterator
import subprocess
import forge.colors as colors
from forge.conf import Config
import os
import json

area_header = re.compile(r"Area\s+Addr.*")
value_header = r"\s+Value\s+Global.*"
delim = r"\s+---.*"


def parse_map_file(lines: Iterator[str]):
    area = None
    symbol_map: Dict[str, Dict[str, str]] = {}
    try:
        while True:
            line = next(lines)
            if re.match(area_header, line) is not None:
                next(lines)  # delimiter
                area = re.split(r"\s+", next(lines))[0]
            elif area is not None:
                if re.match(r"\s{5}\S", line) is not None:
                    value, name = line.strip().split()[:2]
                    symbol_map[area] = symbol_map.get(area, {}) | {
                        # The length of the address must match the decoder exactly
                        name: format(int(value, 16), "#07x"),
                    }

    except StopIteration:
        return symbol_map


def to_var_assignent(value, name):
    return f"var {name} rom[{value}]\n"


def write_cfg_file(map_path: str, config: Config):
    f = open(map_path)
    mjau = parse_map_file(
        iter(list(map(lambda x: x.replace("\n", ""), f.readlines())))
    )

    conf_json = {"symbols": {}}

    with open(config.ucsim_file, "w") as f:
        skipped_areas = ["."]
        if (
            "_sif" in mjau["DATA"].keys()
            or "_sif" in mjau["INITIALIZED"].keys()
        ):
            sif_addr = mjau["DATA"].get(
                "_sif", mjau["INITIALIZED"].get("_sif", None)
            )
            colors.info(f"Enabling simif at {sif_addr}")
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
    json.dump(conf_json, open(config.ucsim_file + ".json", "w"), indent=2)


def launch_sim(config: Config):
    main = os.path.join(config.output_dir, "main.ihx")
    build = subprocess.run(
        ["ninja", main],
    )

    if build.returncode != 0:
        colors.error("compilation failed")
        return

    subprocess.run(
        ["ninja", config.ucsim_file],
        check=True,
    )
    arg = [
        "ucsim_stm8",
        main,
        "-t",
        "STM8S",
        "-C",
        config.ucsim_file,
        "-Z",
        str(config.ucsim_port),
        *config.ucsim_args,
    ]
    colors.info(" ".join(arg))
    try:
        subprocess.run(
            arg,
            check=True,
        )
    except KeyboardInterrupt:
        print()
        colors.info("Simulation interrupted")
