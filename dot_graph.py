""" standalone file to visualize graph lang
"""

from collections.abc import Callable
from io import IOBase
import subprocess
from typing import Any, Tuple
import tempfile

import sys
import os
from logic import split_conjuncts
from typing import TypeVar, Mapping
import ubc
import copy

import syntax


def pretty_name(name):
    # type: (str) -> str
    if "__" not in name:
        return name

    if '.' in name:
        full_name, num = name.split('.')
        if '__' in full_name:
            prog_name, type_info = full_name.split('__')
            return f'{prog_name}<sub>{num}</sub>'
        return name

    c_name, extra = name.split("__")
    return c_name


def fix_func_name(name):
    if name[: len("tmp.")] == "tmp.":
        return name[len("tmp."):]
    return name


# not complete
pretty_opers = {
    "Plus": "+",
    "Minus": "-",
    "Times": "*",
    "Equals": "=",
    "SignedLess": "&lt;<sub>s</sub>",
    "SignedLessEquals": "≤<sub>s</sub>",
    "Or": "or",
    "And": "and",
}

known_typ_change = set(
    ["ROData", "MemAcc", "IfThenElse", "WordArrayUpdate", "MemDom"])


def pretty_expr(expr, print_type=False):
    # type: (syntax.Expr, bool) -> str
    if print_type:
        return "{}:{}".format(pretty_expr(expr), syntax.pretty_type(expr.typ))
    elif expr.kind == "Var":
        return pretty_name(expr.name)
    elif expr.kind == "Num":
        return str(expr.val)
    elif expr.kind == "Op" and expr.name in pretty_opers:
        [x, y] = expr.vals
        return "({} {} {})".format(
            pretty_expr(x, print_type),
            pretty_opers[expr.name],
            pretty_expr(y, print_type),
        )
    elif expr.kind == "Op":
        if expr.name in known_typ_change:
            vals = [pretty_expr(v) for v in expr.vals]
        else:
            vals = [
                pretty_expr(v, print_type=print_type and v.typ != expr.typ)
                for v in expr.vals
            ]
        return "{}({})".format(expr.name, ", ".join(vals))
    elif expr.kind == "Token":
        return "''{}''".format(expr.name)
    else:
        return str(expr)


def pretty_updates(update):
    # type: (Tuple[Tuple[str, syntax.Type], syntax.Expr]) -> str
    (name, typ), expr = update
    return "{} := {}".format(pretty_name(name), pretty_expr(expr))


# black magic
P = TypeVar("P")
R = TypeVar("R")


def viz(t: Callable[[IOBase, P], R]):
    def func(arg: P):
        fd, filepath = tempfile.mkstemp(dir="/tmp/", suffix=".gv")
        t(os.fdopen(fd, 'w'), arg)
        make_and_open_image(filepath)
    return func


@viz
def viz_function(file: IOBase, fun: ubc.Function):
    puts = lambda *args, **kwargs: print(*args, file=file, **kwargs)
    putsf = lambda fmt, * \
        args, **kwargs: print(fmt.format(*args, **kwargs), file=file)

    puts("digraph grph {")
    puts("  node[shape=box]")
    puts(
        f"  FunctionDescription [label=<<u>{fun.name}</u>>] [shape=plaintext]")
    puts()
    for idx, node in fun.nodes.items():
        if isinstance(node, ubc.BasicNode | ubc.CallNode):
            putsf("  {} -> {}", idx, node.succ)
        elif isinstance(node, ubc.CondNode):
            putsf("  {} -> {} [label=T]", idx, node.succ_then)
            if node.succ_else != "Err":
                putsf("  {} -> {} [label=F]", idx, node.succ_else)

        if isinstance(node, ubc.BasicNode):
            content = (
                "<BR/>".join(pretty_updates(u)
                             for u in node.upds) or "<i>empty</i>"
            )
        elif isinstance(node, ubc.CallNode):
            # weird: what is this ghost assertion?
            # TODO: node.rets[0] might be empty
            rets = [r[0] for r in node.rets]
            content = ''
            if len(rets):
                content += f"{', '.join(rets)} := "
            content += "{}({})".format(
                fix_func_name(node.fname),
                ", ".join(
                    pretty_expr(arg)
                    for arg in node.args
                    # if arg.typ.kind != "Builtin" and arg.name != "GhostAssertions"
                ),
            )
        elif isinstance(node, ubc.CondNode):

            if node.succ_else == "Err":
                operands = split_conjuncts(node.expr)
                content = "<b>assert</b> " + pretty_expr(operands[0])
                for operand in operands[1:]:
                    content += "<BR/><b>and</b> " + pretty_expr(operand)
            else:
                content = pretty_expr(node.expr)
        else:
            assert False
        putsf("  {idx} [xlabel={idx}] [label=<{content}>]",
              idx=idx, content=content)

    puts("}")


@viz
def viz_raw_function(file: IOBase, fun: syntax.Function):
    # type: (syntax.Function, Any) -> None
    puts = lambda *args, **kwargs: print(*args, file=file, **kwargs)
    putsf = lambda fmt, * \
        args, **kwargs: print(fmt.format(*args, **kwargs), file=file)

    puts("digraph grph {")
    puts("  node[shape=box]")
    puts(
        f"  FunctionDescription [label=<<u>{fun.name}</u>>] [shape=plaintext]")
    puts()
    for idx, node in fun.nodes.items():
        if node.kind == "Basic" or node.kind == "Call":
            putsf("  {} -> {}", idx, node.cont)
        elif node.kind == "Cond":
            putsf("  {} -> {} [label=T]", idx, node.left)
            if node.right != "Err":
                putsf("  {} -> {} [label=F]", idx, node.right)

        if node.kind == "Basic":
            content = (
                "<BR/>".join(pretty_updates(u)
                             for u in node.upds) or "<i>empty</i>"
            )
        elif node.kind == "Call":
            # weird: what is this ghost assertion?
            # TODO: node.rets[0] might be empty
            rets = [r[0] for r in node.rets]
            content = ''
            if len(rets):
                content += f"{', '.join(rets)} := "
            content += "{}({})".format(
                fix_func_name(node.fname),
                ", ".join(
                    pretty_expr(arg)
                    for arg in node.args
                    # if arg.typ.kind != "Builtin" and arg.name != "GhostAssertions"
                ),
            )
        elif node.kind == "Cond":

            if node.right == "Err":
                operands = split_conjuncts(node.cond)
                content = "<b>assert</b> " + pretty_expr(operands[0])
                for operand in operands[1:]:
                    content += "<BR/><b>and</b> " + pretty_expr(operand)
            else:
                content = pretty_expr(node.cond)
        else:
            assert False
        putsf("  {idx} [xlabel={idx}] [label=<{content}>]",
              idx=idx, content=content)

    puts("}")


@viz
def viz_successor_graph(file: IOBase, all_succs: dict[str, list[str]]):
    puts = lambda *args, **kwargs: print(*args, file=file, **kwargs)
    puts("digraph grph {")
    puts("  node[shape=box]")
    puts()
    for name, succs in all_succs.items():
        for succ in succs:
            puts(f"  {name} -> {succ}")
        puts()
    puts("}")


def make_and_open_image(filepath: str):
    p = subprocess.Popen(
        ["dot", "-n2", "-Tpng", "-O", filepath],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    p.wait()
    assert p.stderr is not None

    if p.returncode != 0:
        print(
            f"ERROR: generated invalid dot graph ({filepath=}):", file=sys.stderr)
        print()
        print("   ", "\n    ".join(p.stderr.read().decode(
            'utf-8').splitlines()), file=sys.stderr)
        exit(3)

    assert p.returncode == 0, (p.returncode, p.stderr.read())
    p = subprocess.Popen(
        ["xdg-open", filepath + ".png"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    p.wait()


if __name__ == "__main__":
    syntax.set_arch()
    if (
        (len(sys.argv) != 3 and len(sys.argv) != 2)
        or "-h" in sys.argv
        or "--help" in sys.argv
    ):
        print("usage: python3 {} <graph_file>".format(__file__), file=sys.stderr)
        print(
            "       python3 {} <graph_file> <function_name>".format(__file__),
            file=sys.stderr,
        )
        exit(1)

    if len(sys.argv) == 3:
        (_, file_name, function_name) = sys.argv
    elif len(sys.argv) == 2:
        (_, file_name) = sys.argv
        function_name = None
    else:
        assert False

    with open(file_name) as f:
        structs, functions_bad_names, const_globals = syntax.parse_and_install_all(
            f, None
        )

    functions = {
        fix_func_name(bad_name): value
        for bad_name, value in functions_bad_names.items()
    }

    if not function_name or function_name not in functions:
        if function_name:
            print("unknown function {!r}".format(
                function_name), file=sys.stderr)
        print("Functions defined in the file: ")
        print(" ", "\n  ".join(functions.keys()), file=sys.stderr)
        exit(2)

    viz_raw_function(functions[function_name])
