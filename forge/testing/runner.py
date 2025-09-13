import subprocess
from forge.conf import Config
from forge.colors import colorize
from forge.testing.simparser import Sim, SimulatorException
from forge.testing.test_setup import get_testcases
from forge.ucsim import build_ucsim_command
import json
import random
import socket
import logging
import os

logger = logging.getLogger(__name__)


class TestRunner:
    def __init__(self, config: Config):
        self.config = config
        build = subprocess.run(
            ["ninja", "test_setup", "build"],
        )

        if build.returncode != 0:
            logger.error("Compilation failed")
            quit(1)

        entries = get_testcases(config)
        if len(entries) == 1:
            logger.warning("No test functions were found in this project")
        self.functions = entries

        with open(config.ucsim.file + ".json") as f:
            self.sim_conf = json.loads(f.read())

        if "simif" not in self.sim_conf:
            logger.error("simlator interface not configured")
            quit(1)

        self.failures = 0

    def run(self, test_function):
        port = random.randint(10000, 60000)

        command = build_ucsim_command(
            ["-q", "-P", "-Z", str(port)], self.config
        )

        logger.debug(" ".join(command))

        instance = subprocess.Popen(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )

        host = "localhost"

        status_addr = "_test_status"

        with socket.socket() as s:
            while True:
                try:
                    s.connect((host, port))
                    break
                except ConnectionRefusedError:
                    pass

            while s.recv(1)[-1] != 0:
                pass  # some non text is sent initially
            sim = Sim(s)
            sim.get_reply()  # Gets the license text

            if sim.get_state().simulation != "stopped":
                logger.error("Simulator not in stopped state")
                quit(1)

            initial_data = sim.get_bytes(
                self.sim_conf["initializer"], self.sim_conf["init_size"]
            )
            sim.set_bytes(self.sim_conf["initialized"], initial_data)
            sim.execute(f"b rom w {status_addr}")
            sim.go(test_function)
            completed = False
            case_failed = False
            assert_triggered = False
            while not completed:
                failed = sim.get_bit(status_addr, 0)
                case_failed = case_failed or failed
                assert_triggered = sim.get_bit(status_addr, 4)
                completed = sim.get_bit(status_addr, 2) or assert_triggered
                if failed:
                    message = sim.get_string("_assert_message")
                    sim.set_bit(status_addr, 0, 0)
                    logger.error(f"{test_function}: {message}")
                if not completed:
                    sim.go("")

            if case_failed:
                self.failures = self.failures + 1
                if assert_triggered:
                    logger.error(
                        f"{test_function}: Failed by assert violation"
                    )
                else:
                    logger.error(f"{test_function}: Some tests failed")
            else:
                logger.info(
                    f"{test_function}: {colorize('All tests passed')} "
                )

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
