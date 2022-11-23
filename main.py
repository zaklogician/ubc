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
    assert_all_kernel_functions_are_reducible()
