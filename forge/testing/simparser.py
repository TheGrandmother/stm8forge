from socket import socket
from dataclasses import dataclass
import re
from typing import Literal

import logging

logger = logging.getLogger(__name__)

chunk_size = 64


@dataclass
class State:
    simulation: str


class Sim:
    def __init__(self, s: socket):
        self.s = s

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
        reply = self.s.recv(chunk_size).decode()
        while reply[-1] != "\0":
            reply += self.s.recv(chunk_size).decode(errors="replace")
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
        self.get_reply()

    def get_bit(self, addr: str, bit: int):
        self.s.sendall(bytes(f"d {addr}.{bit}\n", "utf-8"))
        reply = self.get_reply()
        return reply[-1] == "1"

    def set_bit(self, addr: str, bit: int, val: Literal[0] | Literal[1]):
        self.s.sendall(bytes(f"set bit {addr}.{bit} {val}\n", "utf-8"))
        self.get_reply()

    def kill(self):
        self.s.sendall(bytes(f"kill\n", "utf-8"))
