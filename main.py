from __future__ import print_function
from typing import Tuple, Any, Dict

import sys
import os

sys.path.append(
    os.path.join(os.path.abspath(os.environ.get("TV_ROOT", "..")), "graph-refine")
)

try:
    import syntax
    import logic
except ImportError:
    print("TV_ROOT probably isn't right", file=sys.stderr)
    print(
        "run with 'env TV_ROOT=... python2 ...' (by default, TV_ROOT is assumed to be ...)",
        file=sys.stderr,
    )
    raise

import ubc

if len(sys.argv) != 3:
    print("usage: python2 {} <graph_file.txt> <function_name>".format(__file__))
    exit(2)

graph_file = sys.argv[1]
function_name = sys.argv[2]
ubc.undefined_behaviour_c(graph_file, function_name)
