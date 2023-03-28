""" standalone file to visualize graph lang
"""

import dsa
import logic
from collections.abc import Callable
from io import IOBase
import subprocess
from typing import Any, TypeVar
import tempfile

import sys
import os
import source
import nip


import syntax
from typing_extensions import assert_never
import assume_prove
import ghost_code


def pretty_name(name: Any) -> str:
    if isinstance(name, dsa.Incarnation):
        return _pretty_name(name.base) + f":{name.inc}"

    assert isinstance(name, str)
    return _pretty_name(name)


def _pretty_name(name: str) -> str:
    return name
    # so many bloody cases

    # : -> dsa
    # . -> something i don't wanna throw away
    # __ -> type info I wanna throw away
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
    elif isinstance(expr, source.ExprFunction):
        return f"[smt]{expr.function_name.replace('<', '&lt;').replace('>', '&gt;')}({', '.join(pretty_safe_expr(arg) for arg in expr.arguments)})"
    else:
        return str(expr).replace('<', '&lt;').replace('>', '&gt;')


def pretty_updates(update: tuple[tuple[str, syntax.Type], syntax.Expr]) -> str:
    (name, typ), expr = update
    return "{} := {}".format(pretty_name(name), pretty_expr(expr))


def pretty_safe_update(upd: source.Update[Any]) -> str:
    return "{} := {}".format(pretty_name(upd.var.name), pretty_safe_expr(upd.expr))


P = TypeVar("P")
R = TypeVar("R")


HIDE_ERROR_NODE = True


def viz(t: Callable[[IOBase, P], R]) -> Callable[[P], R]:
    def func(arg: P) -> R:
        # don't use /tmp because stupid snap prevent firefox from opening
        # files in there. Whitelist security is good, but you gotta give an
        # easy way to add things to it stupid snap.
        #
        # So instead, we have to use this raw tmp folder, which I can't even
        # hide with a ., doesn't get to live just in memory nor gets
        # automatically cleaned up by the OS
        tmp_dir = os.path.expanduser('~/tmp.ubc/')
        os.makedirs(tmp_dir, exist_ok=True)
        fd, filepath = tempfile.mkstemp(dir=tmp_dir, suffix=".gv")
        r = t(os.fdopen(fd, 'w'), arg)
        make_and_open_image(filepath)
        return r
    return func


ErrNodeName = 'Err'


@viz
def viz_function(file: IOBase, fun: source.GenericFunction[Any, Any]) -> None:
    puts: Callable[...,
                   None] = lambda *args, **kwargs: print(*args, file=file, **kwargs)

    puts("digraph grph {")
    puts("  node[shape=box]")
    puts("  graph[ranksep=0.3]")
    args = ', '.join(pretty_name(arg.name)
                     for arg in fun.signature.arguments)
    rets = ', '.join(pretty_name(ret.name)
                     for ret in fun.signature.returns)
    font = '[fontname=monospace; fontsize="10px"]'
    # font = '[fontname=monospace]'

    main_label = f"{rets} = <b>{fun.name}</b>({args})"

    # puts(f'  label=<<u>{fun.name}</u><BR ALIGN="LEFT"/><BR ALIGN="LEFT"/>Arguments:<BR ALIGN="LEFT"/>{args}<BR ALIGN="LEFT"/><BR ALIGN="LEFT"/>Returns:<BR ALIGN="LEFT"/>{rets}<BR ALIGN="LEFT"/>>')
    puts(f'  label=<{main_label}>')
    puts(f'  labelloc="t"')
    puts(f'  fontsize="10px"')
    puts(f'  fontname="monospace"')
    # puts(
    #     f'  subgraph func_label {{FunctionName [label=<<u>{fun.name}</u><BR ALIGN="LEFT"/><BR ALIGN="LEFT"/>Arguments:<BR ALIGN="LEFT"/>{args}<BR ALIGN="LEFT"/><BR ALIGN="LEFT"/>Returns:<BR ALIGN="LEFT"/>{rets}<BR ALIGN="LEFT"/>>] [shape=plaintext] {font}}}')
    # puts()

    dom = '[penwidth=3.0 color=darkblue]'
    non_dom = '[color="black"]'
    weights: dict[source.NodeName, int] = {}
    for idx in fun.traverse_topologically(skip_err_and_ret=True):
        node = fun.nodes[idx]
        weights[idx] = max((weights[p]
                            for p in fun.acyclic_preds_of(idx)), default=1)
        if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeEmpty | source.NodeAssume | source.NodeAssert):
            puts(
                f"  {idx} -> {node.succ} {dom if (idx, node.succ) in fun.cfg.back_edges else non_dom}")
        elif isinstance(node, source.NodeCond):
            puts(
                f"  {idx} -> {node.succ_then} [label=T] {font} {dom if (idx, node.succ_then) in fun.cfg.back_edges else non_dom}")
            if not HIDE_ERROR_NODE or node.succ_else != ErrNodeName:
                puts(
                    f"  {idx} -> {node.succ_else} [label=F] {font} {dom if (idx, node.succ_else) in fun.cfg.back_edges else non_dom}")
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

            if HIDE_ERROR_NODE and node.succ_else == ErrNodeName:
                operands = list(source.expr_split_conjuncts(node.expr))
                content = "<b>assert</b>&nbsp;" + pretty_safe_expr(operands[0])
                for operand in operands[1:]:
                    content += "<BR/><b>and</b>&nbsp;" + \
                        pretty_safe_expr(operand)
            else:
                content = pretty_safe_expr(node.expr)
        elif isinstance(node, source.NodeEmpty):
            content = '&lt;empty&gt;'
        elif isinstance(node, source.NodeAssume):
            operands = list(source.expr_split_conjuncts(node.expr))

            content = '<b>assume</b>&nbsp;'
            content += pretty_safe_expr(operands[0])
            for operand in operands[1:]:
                content += "<BR/><b>and</b>&nbsp;" + \
                    pretty_safe_expr(operand)
        elif isinstance(node, source.NodeAssert):
            if isinstance(node, ghost_code.NodePrecondObligationFnCall):
                content = '<b>[hacked assert]</b>&nbsp;' + \
                    pretty_safe_expr(node.expr)
            else:
                content = '<b>assert</b>&nbsp;' + pretty_safe_expr(node.expr)
        else:
            assert_never(node)

        puts(f"  {idx} [xlabel={idx}] [weight={weights[idx]}] {font}")
        if idx == fun.cfg.entry:
            puts(f"[label=<<i>Entry</i>>; penwidth=2]")
        else:
            puts(f"[label=<{content}>]")

    # puts("; {rank=sink bottomlabel [label=foo]}")

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
        ["dot", "-n2", "-Tsvg", "-O", filepath],
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
    # arg subscript don't render nicely on firefox
    # https://bugzilla.mozilla.org/show_bug.cgi?id=308338
    # gotta use chrome
    p = subprocess.Popen(
        # ["chromium", "--new-window", filepath + ".svg"],
        ["open", filepath + ".svg"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    # p.wait()
    # don't wait for p, it only returns once you close the window


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
    func = source.convert_function(
        functions[function_name]).with_ghost(None)
    nip_func = nip.nip(func)
    ghost_func = ghost_code.sprinkle_ghost_code(file_name, nip_func, functions)
    dsa_func = dsa.dsa(ghost_func)
    viz_function(dsa_func)
    assume_prove.pretty_print_prog(
        assume_prove.make_prog(dsa_func))
