from forge.conf import Config
from forge.ninjamaker import standard_flags, stm8_lib_path
from os import path


def write_ccls_file(device: str, conf: Config):
    with open(path.join(conf.src, conf.ccls_file), "w") as f:
        f.write(
            "\n".join(
                [
                    "sdcc",
                    f"%c -mstm8 --std-sdcc99 {standard_flags} -funsigned-char",
                    f"-D {device}",
                    "-D __SDCC",
                    "-D UCSIM",
                    "-I./",
                    f"-I{path.join(conf.std_path, 'inc')}",
                    f"-I{stm8_lib_path}",
                    f"-I{path.join(conf.forge_location, 'lib')}",
                ]
            )
        )
