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
        for func in functions.values():
            if func.entry is None:
                continue
            ubc.dsa(ubc.convert_function(func))
        # func = ubc.convert_function(functions['tmp.' + sys.argv[1]])
        # viz_function(func)
        # func = ubc.dsa(func)
        # viz_function(func)


def same_var_diff_type(func: ubc.Function[ubc.ProgVarName]):
    vars: dict[str, set[ubc.ProgVarName]] = {}
    for n in func.nodes:
        for var in ubc.used_variables_in_node(func.nodes[n]).union(ubc.assigned_variables_in_node(func, n)):
            if '__' in var.name:
                real_name, type_info = var.name.split('__', maxsplit=1)

                if '.' in type_info:
                    real_name += type_info.split('.', maxsplit=1)[1]

                if real_name not in vars:
                    vars[real_name] = set()
                vars[real_name].add(var.name)

    diff = {var: uses for var, uses in vars.items() if len(uses) > 1}
    if diff:
        print(f"diffs: {func.name} {diff}")


with open('examples/kernel_CFunctions.txt') as f:
    kernel_stuff = syntax.parse_and_install_all(
        f, None)


def check_all_kernel():
    with open('examples/kernel_CFunctions.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)

        # f = ubc.convert_function(functions['Kernel_C.Arch_activateIdleThread'])
        # result = ubc.dsa(f)
        # viz_function(f)
        # viz_function(result)
        # return

        for unsafe_func in functions.values():
            if not unsafe_func.entry:
                continue

            func = ubc.convert_function(unsafe_func)
            same_var_diff_type(func)
            dsa_func = ubc.dsa(func)
            ap_prog = ubc.make_assume_prove_prog(dsa_func)

            # func = ubc.convert_function(functions[func])
            # try:
            #     func_dsa = ubc.dsa(func)
            # except Exception as e:
            #     print(len(func.nodes), func.name, repr(e))
            # print('ok', func.name)

        # viz_function(func)
        # func = ubc.dsa(func)
        # viz_function(func)


def view_function(filename: str, function_name: str):
    with open(filename) as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        func = ubc.convert_function(
            functions[function_name])
        dsa_func = ubc.dsa(func)
        # viz_function(func)
        viz_function(dsa_func)


if __name__ == "__main__":
    # view_dsa_example()
    # check_all_kernel()
    func = kernel_stuff[1]['tmp.simple_for_loop']
    prog = ubc.make_assume_prove_prog(ubc.dsa(ubc.convert_function(func)))
    ubc.ap_pretty_print_prog(prog)

    # assert_all_kernel_functions_are_reducible()
    # view_function('examples/dsa.txt', 'tmp.simple_for_loop')
    # view_function('examples/dsa.txt', 'tmp.fail_arr_undefined_behaviour')
    # view_function('examples/kernel_CFunctions.txt', 'Kernel_C.isHighestPrio')
    # view_function('examples/dsa.txt', 'tmp.shift_diag')
    # view_function('examples/kernel_CFunctions.txt', 'Kernel_C.create_untypeds')

    # check_all_kernel()
    # view_function('examples/kernel_CFunctions.txt', 'Kernel_C.strncmp')

    # view_function('examples/dsa.txt', 'tmp.simple_for_loop')
    # view_function('examples/kernel_CFunctions.txt', 'Kernel_C.deriveCap')

    # exit(0)

    # with open('examples/for_loops.txt') as f:
    #     structs, functions, const_globals = syntax.parse_and_install_all(
    #         f, None)
    #     for func in functions.values():
    #         print("function:", func.name)
    #         funcp = ubc.convert_function(func)
    #         for loop_header, loop_data in funcp.loops.items():
    #             print('  ', loop_header, loop_data)
