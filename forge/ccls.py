from forge.conf import Config
from forge.ninjamaker import standard_flags, stm8_lib_path
from os import path


def write_ccls_file(device: str, conf: Config):
    with open(path.join(conf.src, ".ccls"), "w") as f:
        f.writelines(
            [
                "sdcc",
                f"%c -mstm8 --std-sdcc99 {standard_flags}",
                f"-D {device}",
                "-D __SDCC",
                "-I./",
                f"-I{path.join(conf.std_path, 'inc')}",
                f"-I{stm8_lib_path}",
            ]
        )
