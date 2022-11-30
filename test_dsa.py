import pytest
from typing import Collection, Iterable, Mapping, Sequence
from typing_extensions import assert_never
from logic import all_vars_in_set
from main import assert_all_kernel_functions_are_reducible
import ubc
import syntax


with open('examples/kernel_CFunctions.txt') as f:
    kernel_CFunctions = syntax.parse_and_install_all(
        f, None)

with open('examples/dsa.txt') as f:
    example_dsa_CFunctions = syntax.parse_and_install_all(f, None)
del f


def compute_all_path(cfg: ubc.CFG) -> Sequence[Sequence[str]]:
    # binary number, 1 means go left 0 means go right
    # start exploring tree all the way from the left
    all_paths: list[list[str]] = []

    def dfs(n: str):
        all_paths[-1].append(n)

        succs = cfg.all_succs[n]
        if len(succs) == 0:
            return

        if len(succs) == 1 and (n, succs[0]) not in cfg.back_edges:
            dfs(succs[0])
            return

        path_so_far = [n for n in all_paths[-1]]
        for i, succ in enumerate(succs):
            if (n, succ) not in cfg.back_edges:
                if i > 0:
                    all_paths.append(path_so_far)
                dfs(succ)

    for n, preds in cfg.all_preds.items():
        if len(preds) == 0:
            all_paths.append([])
            dfs(n)
    return all_paths


def all_vars_in_expr(expr: ubc.Expr[ubc.VarKind]) -> set[ubc.VarKind]:
    s: set[ubc.VarKind] = set()

    def visitor(expr: ubc.Expr):
        if isinstance(expr, ubc.ExprVar):
            s.add(expr.name)
    ubc.visit_expr(expr, visitor)
    return s


def ensure_exactly_one_assignment_in_path(func: ubc.Function[ubc.DSAVarName], path: Collection[str]):
    """
    This is a bit more complicated than you'd like because we must handle loop
    targets

    Loop targets are only recorded as ProgVarNames, not DSAVarNames.

    Recall that loop targets are havoc'd at the start of loops.

    When we see a loop header, we push it on the loop stack.

    When we read from a variable that hasn't been assigned to yet:
        1. we assert that it was a loop target of a loop on the loop stack.
        2. we remove that loop target from the loop stack
        3. we record that this DSA variable was "assigned"

        (we do 2 and 3 so that you can't use the excuse that a variable is a
        loop target to incarnate it multiple times as different DSA variables.
        A loop target is havoc exactly once, not multiple times).

    When we exit a loop (that is, we are not in one of the loop's body nodes
    anymore), we pop it from the stack. Note that it is possible that not
    every loop target would have been incarnated (ie. we wrote to it directly,
    rather than reading from it first).
    """

    assignments: set[ubc.DSAVarName] = set(arg.name for arg in func.arguments)

    # list of (loop_header, variables that won't ever be assigned)
    loop_stack: list[tuple[str, set[ubc.ProgVarName]]] = []

    def got_assignment(var: ubc.DSAVarName):
        # TODO: when assigning i.n, invalidate all the i.m for m < n. There
        # should only be one. (we can do this because we are walking a single
        # path at a time)
        assert var not in assignments, f"found new assignment for {var}, but it was already defined"
        assignments.add(var)

    for node_name in path:
        if node_name == 'Err' or node_name == 'Ret':
            continue

        node = func.nodes[node_name]

        if func.is_loop_header(node_name):
            loop = func.loops[node_name]
            loop_stack.append((loop.header, set(loop.targets)))

        used_but_unassigned: set[ubc.DSAVarName] = set()
        if isinstance(node, ubc.BasicNode):
            # copy the assignments, because the updates are simultaneous
            # (they don't impact each other).
            base_assignments = set(assignments)
            for upd in node.upds:
                used_but_unassigned |= all_vars_in_expr(
                    upd.expr) - base_assignments
                got_assignment(upd.var.name)

        elif isinstance(node, ubc.CallNode):
            for arg in node.args:
                used_but_unassigned |= all_vars_in_expr(arg) - assignments

            for ret in node.rets:
                got_assignment(ret.name)
        elif isinstance(node, ubc.CondNode):
            used_but_unassigned |= all_vars_in_expr(node.expr) - assignments

        for dsa_var in used_but_unassigned:

            prog_var, num = ubc.unpack_dsa_var_name(dsa_var)
            for loop_header, loop_targets in reversed(loop_stack):
                if prog_var in loop_targets:
                    got_assignment(dsa_var)
                    loop_targets.remove(prog_var)
                    break
            else:
                # we didn't break, ie we didn't find the loop target
                # TODO: Should i even use for/else?
                assert False, f"{dsa_var} wasn't assigned to, yet we read from it (and it's not a valid loop target)"


def ensure_exactly_one_assignment_in_all_path(unsafe_func: syntax.Function):
    plain_func = ubc.convert_function(unsafe_func)
    dsa_func = ubc.dsa(plain_func)

    all_paths = compute_all_path(dsa_func.cfg)
    for i, path in enumerate(all_paths):
        # print(f'path {i}/{len(all_paths)} = {i/len(all_paths)*100:.1f}%')
        ensure_exactly_one_assignment_in_path(dsa_func, path)


@pytest.mark.parametrize('func', (f for f in example_dsa_CFunctions[1].values() if f.entry is not None))
def test_dsa_custom_tests(func: syntax.Function):
    ensure_exactly_one_assignment_in_all_path(func)


# @pytest.mark.skip
@pytest.mark.parametrize('function', (f for f in kernel_CFunctions[1].values() if f.entry is not None))
def test_dsa_kernel_functions(function: syntax.Function):
    if function.name in ('Kernel_C.deriveCap', 'Kernel_C.decodeCNodeInvocation'):
        pytest.skip("there's an assert true that messes DSA up")

    if len(compute_all_path(ubc.convert_function(function).cfg)) > 10000:
        pytest.skip("too many paths, checking them all is too slow")

    ensure_exactly_one_assignment_in_all_path(function)
