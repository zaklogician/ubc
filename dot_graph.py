""" standalone file to visualize graph lang
"""

import nip
from dsa import dsa
import logic
from collections.abc import Callable
from io import IOBase
import subprocess
from typing import Any, Iterator, Tuple, TypeVar, Mapping
import tempfile

import sys
import os
import source

import syntax
from typing_extensions import assert_never
import assume_prove


def pretty_name(name: source.VarNameKind) -> str:
    # so many bloody cases

    # : -> dsa
    # . -> something i don't wanna throw away
    # __ -> type info I wanna throw away
    if isinstance(name, tuple):
        base, inc = name
        return _pretty_name(base) + f"<sub>{inc}</sub>"

    assert isinstance(name, str)
    return _pretty_name(name)


def _pretty_name(name: str) -> str:
    return name
    if "__" not in name:
        return name
    # return name

    name, type_info = name.split('__', maxsplit=1)
    dsa_num = None
    some_num = ''
    if ':' in type_info:
        type_info, dsa_num = type_info.rsplit(':', maxsplit=1)
    if '.' in type_info:
        type_info, some_num = type_info.split('.', maxsplit=1)
        some_num = '.' + some_num

    return name + some_num + (f'<sub>{dsa_num}</sub>' if dsa_num else '')


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


def pretty_expr(expr: syntax.Expr, print_type: bool = False) -> str:
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


def pretty_safe_expr(expr: source.ExprT[Any], print_type: bool = False) -> str:
    if print_type:
        return f"{pretty_safe_expr(expr)}:{syntax.pretty_type(expr.typ)}"
    elif isinstance(expr, source.ExprVar):
        return pretty_name(expr.name)
    elif isinstance(expr, source.ExprNum):
        return str(expr.num)
    elif isinstance(expr, source.ExprOp) and expr.operator.value in pretty_opers:
        [x, y] = expr.operands
        return "({} {} {})".format(
            pretty_safe_expr(x, print_type),
            pretty_opers[expr.operator.value],
            pretty_safe_expr(y, print_type),
        )
    elif isinstance(expr, source.ExprOp):
        if expr.operator.value in known_typ_change:
            vals = [pretty_safe_expr(v) for v in expr.operands]
        else:
            vals = [
                pretty_safe_expr(
                    v, print_type=print_type and v.typ != expr.typ)
                for v in expr.operands
            ]
        return "{}({})".format(expr.operator.value, ", ".join(vals))
    else:
        return str(expr).replace('<', '&lt;').replace('>', '&gt;')


def pretty_updates(update: tuple[tuple[str, syntax.Type], syntax.Expr]) -> str:
    (name, typ), expr = update
    return "{} := {}".format(pretty_name(name), pretty_expr(expr))


def pretty_safe_update(upd: source.Update[source.VarNameKind]) -> str:
    return "{} := {}".format(pretty_name(upd.var.name), pretty_safe_expr(upd.expr))


P = TypeVar("P")
R = TypeVar("R")


def viz(t: Callable[[IOBase, P], R]) -> Callable[[P], R]:
    def func(arg: P) -> R:
        fd, filepath = tempfile.mkstemp(dir="/tmp/", suffix=".gv")
        r = t(os.fdopen(fd, 'w'), arg)
        make_and_open_image(filepath)
        return r
    return func


ErrNodeName = 'Err'


@viz
def viz_function(file: IOBase, fun: source.Function[Any]) -> None:
    puts: Callable[...,
                   None] = lambda *args, **kwargs: print(*args, file=file, **kwargs)

    puts("digraph grph {")
    puts("  node[shape=box]")
    args = '<BR ALIGN="LEFT"/>'.join(pretty_name(arg.name)
                                     for arg in fun.arguments)
    puts(
        f'  FunctionName [label=<<u>{fun.name}</u><BR ALIGN="LEFT"/>{args}>] [shape=plaintext]')
    puts()
    dom = '[penwidth=3.0 color=darkblue]'
    non_dom = '[color="#888"]'
    for idx, node in fun.nodes.items():
        if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeEmpty):
            puts(
                f"  {idx} -> {node.succ} {dom if (idx, node.succ) in fun.cfg.back_edges else non_dom}")
        elif isinstance(node, source.NodeCond):
            puts(
                f"  {idx} -> {node.succ_then} [label=T] {dom if (idx, node.succ_then) in fun.cfg.back_edges else non_dom}")
            if node.succ_else != ErrNodeName:
                puts(
                    f"  {idx} -> {node.succ_else} [label=F] {dom if (idx, node.succ_else) in fun.cfg.back_edges else non_dom}")
        else:
            assert_never(node)

        if isinstance(node, source.NodeBasic):
            content = '<BR/>'.join(pretty_safe_update(upd)
                                   for upd in node.upds)
        elif isinstance(node, source.NodeCall):
            # TODO: node.rets[0] might be empty
            content = ''
            if len(node.rets):
                content += f"{', '.join(pretty_name(r.name) for r in node.rets)} := "
            content += "{}({})".format(
                node.fname,
                ", ".join(
                    pretty_safe_expr(arg)
                    for arg in node.args
                    # if arg.typ.kind != "Builtin" and arg.name != "GhostAssertions"
                ),
            )
        elif isinstance(node, source.NodeCond):

            if node.succ_else == ErrNodeName:
                operands = list(source.expr_split_conjuncts(node.expr))
                content = "<b>assert</b> " + pretty_safe_expr(operands[0])
                for operand in operands[1:]:
                    content += "<BR/><b>and</b> " + pretty_safe_expr(operand)
            else:
                content = pretty_safe_expr(node.expr)
        elif isinstance(node, source.NodeEmpty):
            content = ''
        else:
            assert_never(node)
            assert False
        if idx == fun.cfg.entry:
            puts(f"  {idx} [xlabel={idx}; label=<<i>Entry</i>>; penwidth=2]")
        else:
            puts(f"  {idx} [xlabel={idx}] [label=<{content}>]")

    puts("}")


@viz
def viz_raw_function(file: IOBase, fun: syntax.Function) -> None:
    puts: Callable[...,
                   None] = lambda *args, **kwargs: print(*args, file=file, **kwargs)

    puts("digraph grph {")
    puts("  node[shape=box]")
    puts(
        f"  FunctionDescription [label=<<u>{fun.name}</u>>] [shape=plaintext]")
    puts()
    for idx, node in fun.nodes.items():
        if node.kind == "Basic" or node.kind == "Call":
            puts(f"  {idx} -> {node.cont}")
        elif node.kind == "Cond":
            puts(f"  {idx} -> {node.left} [label=T]")
            if node.right != "Err":
                puts(f"  {idx} -> {node.right} [label=F]")

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
                node.fname,
                ", ".join(
                    pretty_expr(arg)
                    for arg in node.args
                    # if arg.typ.kind != "Builtin" and arg.name != "GhostAssertions"
                ),
            )
        elif node.kind == "Cond":

            if node.right == "Err":
                operands = logic.split_conjuncts(node.cond)
                content = "<b>assert</b> " + pretty_expr(operands[0])
                for operand in operands[1:]:
                    content += "<BR/><b>and</b> " + pretty_expr(operand)
            else:
                content = pretty_expr(node.cond)
        else:
            assert False
        puts(f"  {idx} [xlabel={idx}] [label=<{content}>]")

    puts("}")


@viz
def viz_successor_graph(file: IOBase, all_succs: dict[str, list[str]]) -> None:
    puts: Callable[...,
                   None] = lambda *args, **kwargs: print(*args, file=file, **kwargs)
    puts("digraph grph {")
    puts("  node[shape=box]")
    puts()
    for name, succs in all_succs.items():
        for succ in succs:
            puts(f"  {name} -> {succ}")
        puts()
    puts("}")


def make_and_open_image(filepath: str) -> None:
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

    function_name: str | None
    if len(sys.argv) == 3:
        (_, file_name, function_name) = sys.argv
    elif len(sys.argv) == 2:
        (_, file_name) = sys.argv
        function_name = None
    else:
        assert False

    with open(file_name) as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None
        )

    if not function_name or function_name not in functions:
        if function_name:
            print("unknown function {!r}".format(
                function_name), file=sys.stderr)
        print("Functions defined in the file: ")
        print(" ", "\n  ".join(functions.keys()), file=sys.stderr)
        exit(2)

    # viz_raw_function(functions[function_name])
    # viz_function(source.convert_function(functions[function_name]))
    func = source.convert_function(functions[function_name])
    nip_func = nip.nip(func)
    dsa_func = dsa(nip_func)
    viz_function(dsa_func)
    assume_prove.pretty_print_prog(
        assume_prove.make_prog(dsa_func))
