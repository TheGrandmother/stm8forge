import os
import stat
import shutil
import logging


import forge.tables as tables

logger = logging.getLogger()


def create_openocd_file(model):
    if shutil.which("openocd") is None:
        logger.warning("No executable for openocd was found. Skipping")
        return
    conf = None
    for c in tables.openocd_configs:
        if model.startswith(c.upper()):
            if conf is None or len(c) > len(conf):
                conf = c
    if conf is None:
        logger.warning(
            "There is no suitable openocd config for {model}. Skipping"
        )
        return
    command = (
        "#!/usr/bin/env bash\n"
        + "ninja debug_build\n"
        + "openocd -f /usr/share/openocd/scripts/interface/stlink-dap.cfg "
        + f"-f /usr/share/openocd/scripts/target/{conf}.cfg "
        + '-c "init" -c "reset halt"'
    )
    open("serve_openocd", "w").write(command)

    st = os.stat("serve_openocd")
    os.chmod("serve_openocd", st.st_mode | stat.S_IEXEC)

    logger.success("Wrote openocd command to ./serve_openocd")
