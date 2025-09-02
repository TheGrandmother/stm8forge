import re
from typing import Dict, Iterator
import subprocess
import forge.colors as colors
from forge.conf import Config
from forge.testing.simparser import Sim
import os
import json
import random
import socket
import time


class TestRunner:
    def __init__(self, config: Config):
        self.config = config
        build = subprocess.run(
            ["ninja", "test_setup"],
        )

        if build.returncode != 0:
            colors.error("Compilation failed")
            quit(1)

        with open(config.test_functions_file) as f:
            entries = f.read().split(" ")
            if len(entries) == 1:
                colors.warning("No test functions were found in this project")
            self.functions = entries[1:]  # First is always -xf

        with open(config.ucsim_file + ".json") as f:
            self.sim_conf = json.loads(f.read())

        if "simif" not in self.sim_conf:
            colors.error("simlator interface not configured")
            quit(1)

        self.cases = {}
        self.failures = 0

    def run(self, test_function):
        port = random.randint(10000, 60000)
        args = [
            "ucsim_stm8",
            os.path.join(self.config.output_dir, self.config.target + ".ihx"),
            "-q",
            "-P",
            "-t",
            "STM8S",
            "-C",
            self.config.ucsim_file,
            "-Z",
            str(port),
            *self.config.ucsim_args,
        ]

        instance = subprocess.Popen(
            args, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        # colors.info(f"Started simulator on port {port}")

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
                colors.error("Simulator not in stopped state")
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
                    colors.error(f"{test_function}: {message}")
                if not completed:
                    sim.go("")

            if case_failed:
                self.failures = self.failures + 1
                if assert_triggered:
                    colors.error(
                        f"{test_function}: Failed by assert violation"
                    )
                else:
                    colors.error(f"{test_function}: Some tests failed")
            else:
                colors.success(f"{test_function}: All tests passed ")

            sim.kill()
            while instance.poll() is None:
                pass

    def run_all(self):
        case_count = len(self.functions)
        colors.info(f"==== Found {case_count} tests ====")
        for func in self.functions:
            self.run(func)
        s = f"==== {case_count-self.failures} of {case_count} passed ===="
        if self.failures != 0:
            colors.error(s)
        else:
            colors.success(s)
