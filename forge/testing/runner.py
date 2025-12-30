import json
import logging
import os
import random
import socket
import subprocess

from forge.colors import colorize
from forge.conf import Config
from forge.testing.simparser import Sim, SimulatorException
from forge.testing.test_setup import get_testcases
from forge.ucsim import build_ucsim_command, launch_headless

logger = logging.getLogger(__name__)


class TestRunner:
    def __init__(self, config: Config, selected_files=[]):
        self.config = config
        build = subprocess.run(
            ["ninja", "pre"],
        )

        if build.returncode != 0:
            logger.error("Pre proccessing failed")
            quit(1)

        entries = get_testcases(config, selected_files)
        if len(entries) == 1:
            logger.warning("No test functions were found in this project")
        self.functions = entries

        build = subprocess.run(
            ["ninja", config.ucsim.file, "build"],
            env=os.environ | {"DCE_EXCLUDES": " ".join(self.functions)},
        )

        if build.returncode != 0:
            logger.error("Compilation failed")
            quit(1)

        with open(config.ucsim.file + ".json") as f:
            self.sim_conf = json.loads(f.read())

        if "simif" not in self.sim_conf:
            logger.error("simlator interface not configured")
            quit(1)

        self.failures = 0

    def run(self, test_function):
        port = random.randint(10000, 60000)

        command = build_ucsim_command(["-q", "-P", "-Z", str(port)], self.config)

        logger.debug(" ".join(command))

        instance = subprocess.Popen(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )

        instance, port = launch_headless(self.config, build=False)

        display_name = test_function.replace("_TEST_", "")
        with socket.socket() as s:
            sim = Sim(s, self.config, port)

            sim.execute(f"b rom w {sim.status_addr}")
            sim.go(test_function)
            while not sim.completed:
                sim.get_sim_state()
                completed = sim.completed or sim.assert_triggered
                if sim.failed:
                    message = sim.get_string("_assert_message")
                    sim.set_bit(sim.status_addr, 0, 0)
                    logger.error(f"{display_name}: {message}")
                    break
                if not completed:
                    sim.send("go")

            if sim.failed:
                try:
                    with open(sim.sim_conf["simif"]["out"]) as f:
                        content = f.read()
                        if content != "":
                            logger.info(f"{display_name}: dumping sif file content")
                            logger.warning(content)
                except FileNotFoundError:
                    pass
            else:
                logger.info(f"{display_name}: {colorize('All tests passed')} ")

            sim.kill()
            while instance.poll() is None:
                pass

    def run_all(self):
        case_count = len(self.functions)
        logger.info(f"==== Found {case_count} tests ====")
        for func in self.functions:
            try:
                self.run(func)
            except SimulatorException as e:
                logger.error(f"Failed to execute {func}: {e}")
                self.failures = self.failures + 1

        s = f"==== {case_count-self.failures} of {case_count} passed ===="
        if self.failures != 0:
            logger.error(s)
        else:
            logger.info(colorize(s))
