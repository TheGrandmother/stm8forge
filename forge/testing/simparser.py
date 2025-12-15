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

    def execute_interrupt(self, handler: str):
        # Interupt target is at addr + 7 and is a three byte addr
        # return is at addr + 17
        target_addr = self.symbol(handler)
        return_addr = int(self.send("PC"))
        base_addr = self.symbol("__INTER")
        self.set_bytes(base_addr + 7, target_addr.to_bytes(3))
        self.set_bytes(base_addr + 17, return_addr.to_bytes(2))
        self.send("dc __INTER")
        self.send(f"tbreak {hex(return_addr)}")
        self.send("go __INTER")

    def symbol(self, symbol: str) -> int:
        return int(self.sim_conf["symbols"][symbol], 16)

    def get_i8(self, addr: int | str, signed=False) -> int:
        return int.from_bytes(self.get_bytes(addr, 1), signed=signed)

    def get_i16(self, addr: int | str, signed=False) -> int:
        return int.from_bytes(self.get_bytes(addr, 2), signed=signed)

    def get_i32(self, addr: int | str, signed=False) -> int:
        return int.from_bytes(self.get_bytes(addr, 4), signed=signed)

    def get_i64(self, addr: int | str, signed=False) -> int:
        return int.from_bytes(self.get_bytes(addr, 8), signed=signed)

    def get_bytes(self, addr: int | str, count):
        lit_addr = addr
        if type(addr) == str:
            if addr.startswith("0x"):
                lit_addr = int(addr, 16)
            elif addr[0].isdigit():
                lit_addr = int(addr)
            elif addr in self.sim_conf["symbols"]:
                lit_addr = int(self.sim_conf["symbols"][addr], 16)
            else:
                resp = self.send(f"i v {addr}")
                if resp.startswith(addr):
                    lit_addr = int(resp.split("[")[1].split("]")[0], 16)
                else:
                    raise SimulatorException(
                        f"Addr {addr} can not be resolved to a nice number"
                    )

        end = lit_addr + count

        self.s.sendall(
            bytes(
                f"d /h rom {lit_addr} {end} {count}\n",
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
