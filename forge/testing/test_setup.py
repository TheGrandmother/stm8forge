from pycparser import c_ast, parse_file
from typing import List


class FuncCallVisitor(c_ast.NodeVisitor):
    def __init__(self):
        pass

    def visit_FuncDef(self, node):
        print(f"{node.decl.name}")

    def generic_visit(self, node):
        print(node)


def show_func_defs(filename, cpp_args):
    print(filename, cpp_args)
    print(f"sdcpp {filename} {cpp_args}")
    ast = parse_file(
        filename, use_cpp=True, cpp_path="sdcpp", cpp_args=cpp_args.split(" ")
    )
    v = FuncCallVisitor()
    v.visit(ast)
