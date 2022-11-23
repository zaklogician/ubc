from typing import Tuple, Any, Dict

import sys
import os
from dot_graph import viz_function

import syntax
import ubc

syntax.set_arch('rv64')


def non_reachable_nodes(fun: syntax.Function) -> set[str]:
    assert fun.entry is not None
    q: list[str] = [fun.entry]
    visited = set()
    while q:
        n = q.pop(0)
        if n not in fun.nodes:
            continue
        visited.add(n)
        for cont in fun.nodes[n].get_conts():
            if cont not in visited:
                q.append(cont)

    return set(fun.nodes.keys()) - set(visited)


def has_loop(cfg):
    visited = set()
    q: list[str] = [cfg.entry]
    while q:
        n = q.pop(0)
        if n in visited:
            continue

        # Visit in topological order, that is, visit all the predecessors first.
        if all(p in visited for p in cfg.all_preds[n]):
            visited.add(n)
            q += cfg.all_succs[n]
    return len(visited) < len(cfg.all_preds)


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
