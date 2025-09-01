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

    def run(self, test_function):
        port = random.randint(10000, 60000)
        args = [
            "ucsim_stm8",
            os.path.join(self.config.output_dir, self.config.target + ".ihx"),
            "-P",
            "-t",
            "STM8S",
            "-q",
            "-C",
            self.config.ucsim_file,
            "-Z",
            str(port),
            *self.config.ucsim_args,
        ]

        instance = subprocess.Popen(args, stdout=subprocess.PIPE)
        colors.info(f"Started on port {port}")
        time.sleep(0.5)

        host = "localhost"

        got_license = False

        with socket.socket() as s:
            s.connect((host, port))
            while s.recv(1)[-1] != 0:
                pass  # some non text is sent initially
            sim = Sim(s)
            sim.get_reply()  # Gets the license text

            state = sim.get_state()
            if state.simulation != "stopped":
                colors.error("Simulator not in stopped state")
                quit(1)

            sim.execute("b rom w _test_status")
            completed = False
            passed = False
            failed = False
            sim.go(test_function)
            while not completed:
                failed = sim.get_bit("_test_status", 0)
                passed = sim.get_bit("_test_status", 1)
                completed = sim.get_bit("_test_status", 2)
                if failed:
                    with open(self.sim_conf["simif"]["out"]) as f:
                        lines = f.readlines()
                        colors.error(f"{lines[0][:-1]}")
                if not completed:
                    sim.go("")

            if passed and not failed:
                colors.success(f"{test_function}")
            if failed:
                colors.error(f"{test_function} NOT OK")
            sim.kill()
            while instance.poll() is None:
                pass
            print(instance.returncode)

    def run_all(self):
        for func in self.functions:
            self.run(func)
