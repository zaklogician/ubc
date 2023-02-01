from enum import Enum
from typing import Collection, Sequence, Tuple, Any, Dict

import sys
import os
from typing_extensions import assert_never
from dot_graph import viz_function

import syntax
import source
import abc_cfg
import smt
import dsa
import nip
import assume_prove

syntax.set_arch('rv64')


def assert_all_kernel_functions_are_reducible() -> None:
    with open('examples/kernel_CFunctions.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        for unsafe_func in functions.values():
            if not unsafe_func.entry:
                continue
            func = source.convert_function(unsafe_func)
            assert abc_cfg.is_reducible(func.cfg)
    print("[check] all kernel functions with an entry are reducible")


def same_var_diff_type(func: source.Function[source.ProgVarName]) -> None:
    vars: dict[str, set[source.ProgVarName]] = {}
    for n in func.nodes:
        for var in source.used_variables_in_node(func.nodes[n]).union(source.assigned_variables_in_node(func, n)):
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


class CmdlineOption(Enum):
    SHOW_GRAPH = '--show-graph'
    """ Show the graph lang """
    SHOW_DSA = '--show-dsa'
    """ Show the graph after having applied dynamic single assignment """
    SHOW_NIP = '--show-nip'
    """ Show the non-initialized protected graph """
    SHOW_AP = '--show-ap'
    """ Show the assume prove prog """
    SHOW_SMT = '--show-smt'
    """ Show the SMT given to the solvers """
    SHOW_SATS = '--show-sats'
    """ Show the raw results from the smt solvers (sat/unsat) """

    SHOW_LINE_NUMBERS = '--ln'
    """ Shows line numbers for the smt """


def find_functions_by_name(function_names: Collection[str], target: str) -> str:
    if target in function_names:
        return target

    for option in function_names:
        if option.endswith(target) and len(option) > len(target) and option[-len(target) - 1] == '.':
            return option

    selected: str | None = None
    for option in function_names:
        if target in option:
            if selected is None:
                selected = option
            else:
                print(
                    f"{target} doesn't allow me to chose between {selected} and {option}")
                print(f"Use a more specific name")
                exit(1)
    if selected is None:
        print(f"{target} didn't match any function name")
        print(f"The list of available functions is")
        print('\n'.join(function_names))
        exit(1)
    return selected


def run(filename: str, function_names: Collection[str], options: Collection[CmdlineOption]) -> None:
    if filename.lower() == 'dsa':
        filename = 'examples/dsa.txt'
    elif filename.lower() == 'kernel':
        filename = 'examples/kernel_CFunctions.txt'

    if os.path.isfile(filename):
        with open(filename) as f:
            stuff = syntax.parse_and_install_all(f, None)
    else:
        print(f"filename {filename} should be the path of a file")
        exit(1)

    if len(function_names) == 0:
        print("list of functions in the file")
        for func in stuff[1].values():
            print(f'  {func.name} ({len(func.nodes)} nodes)')

    _, functions, _ = stuff

    for name in function_names:
        unsafe_func = functions[find_functions_by_name(functions.keys(), name)]

        prog_func = source.convert_function(unsafe_func)
        if CmdlineOption.SHOW_GRAPH in options:
            viz_function(prog_func)

        nip_func = nip.nip(prog_func)
        if CmdlineOption.SHOW_NIP in options:
            viz_function(nip_func)

        dsa_func = dsa.dsa(nip_func)
        if CmdlineOption.SHOW_DSA in options:
            viz_function(dsa_func)

        prog = assume_prove.make_prog(dsa_func)
        if CmdlineOption.SHOW_AP in options:
            assume_prove.pretty_print_prog(prog)

        smtlib = smt.make_smtlib(prog)
        if CmdlineOption.SHOW_SMT in options:
            if CmdlineOption.SHOW_LINE_NUMBERS in options:
                lines = smtlib.splitlines()
                w = len(str(len(lines)))
                for i, line in enumerate(lines):
                    print(f'{str(i).rjust(w)}  {line}')
            else:
                print(smtlib)

        sats = tuple(smt.send_smtlib_to_z3(smtlib))
        if CmdlineOption.SHOW_SATS in options:
            print(sats)

        assert len(sats) == 2
        result = smt.parse_sats(sats)
        if result is smt.VerificationResult.OK:
            print("verification succeeded", file=sys.stderr)
            exit(0)
        elif result is smt.VerificationResult.INCONSTENT:
            print("INTERNAL ERROR: smt is an inconsistent state", file=sys.stderr)
            exit(2)
        elif result is smt.VerificationResult.FAIL:
            print("verification failed (good luck figuring out why)", file=sys.stderr)
            exit(1)
        else:
            assert_never(result)


def usage() -> None:
    print('usage: python3 main.py [options] <graphfile.txt> function-names...')
    print()
    print('  --show-graph: Show the graph lang')
    print('  --show-dsa: Show the graph after having applied dynamic single assignment')
    print('  --show-ap: Show the assume prove prog')
    print('  --show-smt: Show the SMT given to the solvers')
    print('  --show-sats: Show the raw results from the smt solvers (sat/unsat)')
    exit(0)


def main() -> None:
    if '--help' in sys.argv or '-h' in sys.argv or len(sys.argv) == 1:
        usage()

    options: list[CmdlineOption] = []
    function_names: list[str] = []
    for arg in sys.argv[1:]:
        if arg in (opt.value for opt in CmdlineOption):
            options.append(CmdlineOption(arg))
        elif arg.startswith('-'):
            print(f'err: unknown option {arg}')
            print()
            usage()
        else:
            function_names.append(arg)

    if len(function_names) == 0:
        print("err: you need to specify at least the graphfile")
        print()
        usage()

    filename = function_names[0]
    function_names = function_names[1:]
    run(filename, function_names, options)


if __name__ == "__main__":
    main()
