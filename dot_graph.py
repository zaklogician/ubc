# -*- coding: utf-8 -*-

# I'm aware of dot utils but it says it produces missleading graphs
# at least I know what this does

# open /tmp/grph.png

from __future__ import print_function
import subprocess
from typing import Any, Tuple

import sys
import os

os.environ.get("TV_ROOT", "..")
sys.path.append(
    os.path.join(os.path.abspath(os.environ.get("TV_ROOT", "..")), "graph-refine")
)

try:
    import syntax
except ImportError:
    print("TV_ROOT probably isn't right", file=sys.stderr)
    print(
        "run with 'env TV_ROOT=... python2 ...' (by default, TV_ROOT is assumed to be ...)",
        file=sys.stderr,
    )
    raise

subprocess.DEVNULL = open(os.devnull)  # python2 hack


def pretty_name(name):
    # type: (str) -> str
    if "__" not in name:
        return name
    c_name, extra = name.split("__")
    return c_name


def fix_func_name(name):
    if name[: len("tmp.")] == "tmp.":
        return name[len("tmp.") :]
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
}

known_typ_change = set(["ROData", "MemAcc", "IfThenElse", "WordArrayUpdate", "MemDom"])


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
        assert False, "not pretty printable"


def pretty_updates(update):
    # type: (Tuple[Tuple[str, syntax.Type], syntax.Expr]) -> str
    (name, typ), expr = update
    return "{} := {}".format(pretty_name(name), pretty_expr(expr))


def dot_graph(fun, file):
    # type: (syntax.Function, Any) -> None
    puts = lambda *args, **kwargs: print(*args, file=file, **kwargs)
    putsf = lambda fmt, *args, **kwargs: print(fmt.format(*args, **kwargs), file=file)

    puts("digraph grph {")
    puts("  node[shape=box]")
    puts()
    for idx in fun.nodes:
        node = fun.nodes[idx]
        if node.kind == "Basic" or node.kind == "Call":
            putsf("  {} -> {}", idx, node.cont)
        elif node.kind == "Cond":
            putsf("  {} -> {} [label=T]", idx, node.left)
            putsf("  {} -> {} [label=F]", idx, node.right)

        if node.kind == "Basic":
            content = (
                "<br>".join(pretty_updates(u) for u in node.upds) or "<i>empty</i>"
            )
        elif node.kind == "Call":
            # weird: what is this ghost assertion?
            content = "{} := {}({})".format(
                pretty_name(node.rets[0][0]),
                fix_func_name(node.fname),
                ", ".join(
                    pretty_expr(arg)
                    for arg in node.args
                    if arg.typ.kind != "Builtin" and arg.name != "GhostAssertions"
                ),
            )
        elif node.kind == "Cond":
            content = pretty_expr(node.cond)
        else:
            assert False
        # content = content.replace('<', '&lt;').replace('>', '&gt;')
        putsf("  {idx} [xlabel={idx}] [label=<{content}>]", idx=idx, content=content)

    puts("}")


def make_image(fun):
    with open("/tmp/grph.gv", "w") as f:
        dot_graph(fun, f)

    p = subprocess.Popen(
        ["dot", "-n2", "-Tpng", "-O", "/tmp/grph.gv"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    p.wait()
    if p.returncode != 0:
        print("ERROR: generated invalid dot graph:", file=sys.stderr)
        print()
        print("   ", "\n    ".join(p.stderr.read().splitlines()), file=sys.stderr)
        exit(3)

    assert p.returncode == 0, (p.returncode, p.stderr.read())
    p = subprocess.Popen(
        ["xdg-open", "/tmp/grph.gv.png"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    p.wait()


if __name__ == "__main__":
    if (
        (len(sys.argv) != 3 and len(sys.argv) != 2)
        or "-h" in sys.argv
        or "--help" in sys.argv
    ):
        print("usage: python2 {} <graph_file>".format(__file__), file=sys.stderr)
        print(
            "       python2 {} <graph_file> <function_name>".format(__file__),
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
        for bad_name, value in functions_bad_names.iteritems()
    }

    if not function_name or function_name not in functions:
        if function_name:
            print("unknown function {!r}".format(function_name), file=sys.stderr)
        print("Functions defined in the file: ")
        print(" ", "\n  ".join(functions.keys()), file=sys.stderr)
        exit(2)

    make_image(functions[function_name])
