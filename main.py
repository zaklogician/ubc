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
        for unsafe_func in functions.values():
            if not unsafe_func.entry:
                continue
            func = ubc.convert_function(unsafe_func)
            assert ubc.cfg_is_reducible(func.cfg)
    print("[check] all kernel functions with an entry are reducible")


def view_dsa_example():
    with open('examples/dsa.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        func = ubc.convert_function(functions['tmp.' + sys.argv[1]])
        viz_function(func)
        func = ubc.dsa(func)
        viz_function(func)


def check_all_kernel():
    with open('examples/kernel_CFunctions.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)

        # f = ubc.convert_function(functions['Kernel_C.Arch_activateIdleThread'])
        # result = ubc.dsa(f)
        # viz_function(f)
        # viz_function(result)
        # return

        for func in functions:
            # print('doing', functions[func].name)
            if not functions[func].entry:
                continue
            func = ubc.convert_function(functions[func])
            try:
                func_dsa = ubc.dsa(func)
            except Exception as e:
                print(len(func.nodes), func.name, repr(e))
            # print('ok', func.name)

        # viz_function(func)
        # func = ubc.dsa(func)
        # viz_function(func)


if __name__ == "__main__":

    # assert_all_kernel_functions_are_reducible()

    check_all_kernel()

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
