import logging
import os
import re
from typing import List

from pycparser import CParser, c_ast

from forge.conf import Config

logger = logging.getLogger(__name__)


class FuncCallVisitor(c_ast.NodeVisitor):
    names: List[str]

    def __init__(self):
        self.names = []

    def visit_FuncDef(self, node):
        if node.decl.name.startswith("TEST"):
            self.names.append("_" + node.decl.name)


def show_func_defs(filename):
    with open(filename) as f:
        text = f.read()
        # PyCparse cannot handle __trap and __interrupt constructs
        text = re.sub(
            r"__interrupt\(.*\)",
            "",
            text.replace("__trap", ""),
            0,
            re.MULTILINE,
        )
        parser = CParser()
        try:
            ast = parser.parse(text, filename)
            v = FuncCallVisitor()
            v.visit(ast)
            return v.names
        except Exception as e:
            logger.warning(f"Could not find test declarations in {filename}: {e}")
            return []


def get_testcases(config: Config, selected_files: List[str] = []):

    if selected_files != []:
        sources = (
            os.path.join(config.output_dir, "pre", file) for file in selected_files
        )
    else:
        sources = (
            os.path.join(config.output_dir, "pre", file)
            for file in os.listdir(os.path.join(config.output_dir, "pre"))
            if file.endswith("_test.c")
        )

    names = []
    for s in sources:
        names += show_func_defs(s)

    return names
