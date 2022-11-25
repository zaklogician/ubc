from typing import Tuple, Any, Dict

import sys
import os
from dot_graph import viz_function

import syntax
import ubc

syntax.set_arch('rv64')


def assert_all_kernel_functions_are_reducible():
    with open('examples/kernel_CFunctions.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        for func in functions.values():
            if not func.entry:
                continue
            cfg = ubc.compute_cfg_from_func(func)
            assert ubc.cfg_is_reducible(cfg)
    print("[check] all kernel functions with an entry are reducible")


if __name__ == "__main__":
    with open('examples/dsa.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        func = ubc.convert_function(functions['tmp.' + sys.argv[1]])
        viz_function(func)
        func = ubc.dsa(func)
        viz_function(func)

    exit(0)

    assert_all_kernel_functions_are_reducible()

    exit(0)

    with open('examples/for_loops.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        func = ubc.convert_function(functions['tmp.loop_write_single'])
        print(func.loops)
    exit(0)

    with open('examples/for_loops.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        for func in functions.values():
            print("function:", func.name)
            funcp = ubc.convert_function(func)
            for loop_header, loop_data in funcp.loops.items():
                print('  ', loop_header, loop_data)
