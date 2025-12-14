import json
import logging
import re
from dataclasses import dataclass
from socket import socket
from time import monotonic
from typing import Literal

from forge.conf import Config

logger = logging.getLogger(__name__)

chunk_size = 64


class SimulatorException(Exception):
    pass


class FunctionCallError(SimulatorException):
    pass


@dataclass
class State:
    simulation: str


class Sim:
    def __init__(self, s: socket, config: Config, port: int):

        start = monotonic()

        self.s = s

        with open(config.ucsim.file + ".json") as f:
            self.sim_conf = json.loads(f.read())

        if "simif" not in self.sim_conf:
            raise SimulatorException("simlator interface not configured")

        logger.debug("Connecting to μCsim")

        while True:
            try:
                s.connect(("localhost", port))
                break
            except ConnectionRefusedError:
                if monotonic() - start > 5:
                    raise SimulatorException("Connection timeout")

        logger.debug("Connected to simulator")

        while s.recv(1)[-1] != 0:
            pass  # some non text is sent initially

        logger.debug("Initial garbage parsed")

        self.get_reply()  # Gets the license text

        logger.debug("License text received")

        state = self.get_state().simulation
        if state != "stopped":
            raise SimulatorException("Simulator started in state: {state}")

        initial_data = self.get_bytes(
            self.sim_conf["initializer"], self.sim_conf["init_size"]
        )

        logger.debug(f"Got {len(initial_data)} bytes to init")

        self.set_bytes(self.sim_conf["initialized"], initial_data)

        logger.debug("Initialization completed")

    def get_bytes(self, start, count):
        start = int(start, 16)
        stop = start + count - 1
        self.s.sendall(
            bytes(
                f"d /h {start} {stop} {count}\n",
                "utf-8",
            )
        )
        reply = self.get_reply()
        b = map(lambda x: int(x, 16), reply.split(" ")[1 : count + 1])
        return bytes(b)

    def set_bytes(self, addr, data: bytes):
        hexes = map(lambda x: format(x, "d"), data)
        self.s.sendall(
            bytes(
                f"set mem rom {addr} {' '.join(hexes)}\n",
                "utf-8",
            )
        )
        self.get_reply()

    def get_string(self, addr):
        self.s.sendall(
            bytes(
                f"d /s {addr}\n",
                "utf-8",
            )
        )
        return self.get_reply()

    def get_reply(self):
        start = monotonic()
        reply = self.s.recv(chunk_size).decode()
        while reply[-1] != "\0":
            reply += self.s.recv(chunk_size).decode(errors="replace")
            if monotonic() - start > 1:
                raise SimulatorException("Reply timeout")
        return reply.replace("\r", "").split("\n", 1)[1][:-2]

    def get_state(self) -> State:
        regex = r"(.|\n)*((?:Simulation: )(?P<simulation>.*))\n.*"
        self.s.sendall(bytes("state\n", "utf-8"))
        reply = self.get_reply()
        match = re.match(regex, reply, re.MULTILINE)
        if match is None:
            raise Exception("Failed to parse")

        return State(**match.groupdict())

    def execute(self, command: str):
        self.s.sendall(bytes(command + "\n", "utf-8"))
        reply = self.get_reply()
        if reply != "":
            logger.error(f"Failed to execute {command}")
            logger.error(f"Reply: {reply}")
            quit(1)

    def send(self, command: str):
        self.s.sendall(bytes(command + "\n", "utf-8"))
        return self.get_reply()

    def go(self, addr: str):
        self.s.sendall(bytes(f"r {addr}\n", "utf-8"))
        reply = self.get_reply()
        if reply.startswith("Error"):
            raise FunctionCallError(reply)

    def get_bit(self, addr: str, bit: int):
        self.s.sendall(bytes(f"d {addr}.{bit}\n", "utf-8"))
        reply = self.get_reply()
        return reply[-1] == "1"

    def set_bit(self, addr: str, bit: int, val: Literal[0] | Literal[1]):
        self.s.sendall(bytes(f"set bit {addr}.{bit} {val}\n", "utf-8"))
        self.get_reply()

    def kill(self):
        self.s.sendall(bytes(f"kill\n", "utf-8"))
