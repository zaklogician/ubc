from __future__ import print_function
from pprint import pprint
from typing import Tuple, Any, Dict

import sys
import os

os.environ.get("TV_ROOT", "..")
sys.path.append(
    os.path.join(os.path.abspath(os.environ.get("TV_ROOT", "..")), "graph-refine")
)

try:
    import syntax
except ImportError:
    print("TV_ROOT probably isn't right", file=sys.stderr)
    print(
        "run with 'env TV_ROOT=... python2 ...' (by default, TV_ROOT is assumed to be ...)",
        file=sys.stderr,
    )
    raise

if len(sys.argv) != 2:
    print("usage: python2 {} <graph_file.txt>".format(__file__))
    exit(2)
graph_file = sys.argv[1]

with open(graph_file) as f:
    struct, functions, const_globals = syntax.parse_and_install_all(f, None)

    print(struct)
    print(functions)
    print(const_globals)

    add = functions["tmp.add"]
    for node in add.nodes.values():
        # print(node)
        if node.kind == "Basic":
            for ((name, typ), expr) in node.upds:
                print(name, typ, syntax.pretty_expr(expr))
        elif node.kind == "Cond":
            print(
                "Cond",
                syntax.pretty_expr(node.cond),
                "?",
                node.left,
                ":",
                node.right,
            )
