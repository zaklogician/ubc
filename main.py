from typing import Tuple, Any, Dict

import sys
import os

import ubc

if len(sys.argv) != 3:
    print("usage: python3 {} <graph_file.txt> <function_name>".format(__file__))
    exit(2)

graph_file = sys.argv[1]
function_name = sys.argv[2]
ubc.undefined_behaviour_c(graph_file, function_name)
