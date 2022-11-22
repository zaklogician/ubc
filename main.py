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

with open('examples/kernel_CFunctions.txt') as f:
    structs, functions, const_globals = syntax.parse_and_install_all(f, None)


    # func = functions['Kernel_C.strnlen']
    # ubc.remove_contradiction_entry_node(func)
    # cfg = ubc.compute_cfg_from_func(func)
    # print(cfg, ubc.cfg_is_reducible(cfg))
    # print(cfg.all_doms)

    # exit(0)
    irreducible_functions = []

    for i, (fname, func) in enumerate(functions.items()):
        if func.entry is None:
            # print(f"no entry point; skip {fname}")
            continue

        ubc.remove_contradiction_entry_node(func)
        cfg = ubc.compute_cfg_from_func(func)
        assert non_reachable_nodes(func) == set()

        if ubc.cfg_is_reducible(cfg):
            print(f"ok {fname}")
        continue
        # else:
        #     print(f".  {fname}")
        if not ubc.cfg_is_reducible(cfg):
            irreducible_functions.append(func)

    num_nodes = lambda a: len(a.nodes)
    for func in sorted(irreducible_functions, key=num_nodes):
        print('irr', func.name)

# if len(sys.argv) != 3:
#     print("usage: python3 {} <graph_file.txt> <function_name>".format(__file__))
#     exit(2)

# graph_file = sys.argv[1]
# function_name = sys.argv[2]
# ubc.undefined_behaviour_c(graph_file, function_name)

