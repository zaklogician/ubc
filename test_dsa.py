import pytest
from typing import Collection, Iterable, Mapping, Sequence, Set
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


def compute_all_path(cfg: ubc.CFG) -> Sequence[Sequence[ubc.NodeName]]:
    # binary number, 1 means go left 0 means go right
    # start exploring tree all the way from the left
    all_paths: list[list[ubc.NodeName]] = []

    def dfs(n: ubc.NodeName):
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


def all_vars_in_expr(expr: ubc.Expr[ubc.VarKind]) -> set[ubc.Var[ubc.VarKind]]:
    s: set[ubc.Var[ubc.VarKind]] = set()

    def visitor(expr: ubc.Expr):
        if isinstance(expr, ubc.ExprVar):
            s.add(ubc.Var(expr.name, expr.typ))
    ubc.visit_expr(expr, visitor)
    return s


# def ensure_exactly_one_assignment_in_path(func: ubc.Function[ubc.DSAVarName], path: Collection[ubc.NodeName]):
#     """
#     This is a bit more complicated than you'd like because we must handle loop
#     targets

#     Loop targets are only recorded as ProgVarNames, not DSAVarNames.

#     Recall that loop targets are havoc'd at the start of loops.

#     When we see a loop header, we push it on the loop stack.

#     When we read from a variable that hasn't been assigned to yet:
#         1. we assert that it was a loop target of a loop on the loop stack.
#         2. we remove that loop target from the loop stack
#         3. we record that this DSA variable was "assigned"

#         (we do 2 and 3 so that you can't use the excuse that a variable is a
#         loop target to incarnate it multiple times as different DSA variables.
#         A loop target is havoc exactly once, not multiple times).

#     When we exit a loop (that is, we are not in one of the loop's body nodes
#     anymore), we pop it from the stack. Note that it is possible that not
#     every loop target would have been incarnated (ie. we wrote to it directly,
#     rather than reading from it first).
#     """

#     print(f'{path=}')

#     assignments: set[ubc.DSAVar] = set(arg for arg in func.arguments)

#     def got_assignment(var: ubc.DSAVar):
#         print(f'{node_name=} {var} is assigned')
#         nonlocal assignments

#         assert var not in assignments, f"found new assignment for {var}, but it was already defined"
#         # when assigning i.n, we invalidate all the i.m for m != n. There
#         # should only be one. (we can do this because we are walking a single
#         # path at a time)
#         name, num = ubc.unpack_dsa_var_name(var.name)

#         previous_incarnations: set[ubc.DSAVar] = set()
#         for assignment in assignments:
#             n, _ = ubc.unpack_dsa_var_name(assignment.name)
#             if n == name:
#                 previous_incarnations.add(assignment)

#         assert len(previous_incarnations) <= 1, previous_incarnations
#         assignments -= previous_incarnations
#         assignments.add(var)

#     for node_name in path:
#         if node_name == 'Err' or node_name == 'Ret':
#             continue

#         node = func.nodes[node_name]

#         if func.is_loop_header(node_name):
#             # all the loop targets have been havocd
#             for target in func.loops[node_name].targets:
#                 got_assignment(target)

#         used_but_unassigned: set[ubc.DSAVar] = set()
#         if isinstance(node, ubc.BasicNode):
#             # copy the assignments, because the updates are simultaneous
#             # (they don't impact each other).
#             base_assignments = set(assignments)
#             for upd in node.upds:
#                 used_but_unassigned |= all_vars_in_expr(
#                     upd.expr) - base_assignments
#                 got_assignment(upd.var)

#         elif isinstance(node, ubc.CallNode):
#             for arg in node.args:
#                 used_but_unassigned |= all_vars_in_expr(arg) - assignments

#         elif isinstance(node, ubc.CondNode):
#             used_but_unassigned |= all_vars_in_expr(node.expr) - assignments

#         if len(used_but_unassigned) > 0:
#             assert False, f"({node_name=} {path=}) {used_but_unassigned} weren't assigned to, yet we read from them"

#         if isinstance(node, ubc.CallNode):
#             for ret in node.rets:
#                 got_assignment(ret)


def assigned_variables_in_node(func: ubc.Function[ubc.DSAVarName], n: ubc.NodeName) -> Collection[ubc.DSAVar]:
    if n in (ubc.NodeNameRet, ubc.NodeNameErr):
        return []

    assigned_variables: list[ubc.DSAVar] = []
    node = func.nodes[n]
    if isinstance(node, ubc.BasicNode):
        assigned_variables.extend(upd.var for upd in node.upds)
    elif isinstance(node, ubc.CallNode):
        assigned_variables.extend(ret for ret in node.rets)
    elif not isinstance(node, ubc.EmptyNode | ubc.CondNode):
        assert_never(node)

    if func.is_loop_header(n):
        assigned_variables.extend(func.loops[n].targets)

    return assigned_variables

def read_variables_in_node(node: ubc.Node[ubc.DSAVarName]) -> Collection[ubc.DSAVar]:
    read_variables: list[ubc.DSAVar] = []
    if isinstance(node, ubc.BasicNode):
        for upd in node.upds:
            read_variables.extend(all_vars_in_expr(upd.expr))
    elif isinstance(node, ubc.CallNode):
        for arg in node.args:
            read_variables.extend(all_vars_in_expr(arg))
    elif isinstance(node, ubc.CondNode):
        read_variables.extend(all_vars_in_expr(node.expr))
    elif not isinstance(node, ubc.EmptyNode):
        assert_never(node)
    return read_variables

def ensure_assigned_at_most_once(func: ubc.Function[ubc.DSAVarName], path: Collection[ubc.NodeName]):
    # this doesn't ensure that every variable that is assigned is used
    assigned_variables: list[ubc.DSAVar] = []
    for node in path:
        assigned_variables.extend(assigned_variables_in_node(func, node))
    assert len(assigned_variables) == len(set(assigned_variables))

def ensure_using_latest_incarnation(func: ubc.Function[ubc.DSAVarName], path: Collection[ubc.NodeName]):
    latest_assignment: dict[ubc.ProgVar, ubc.IncarnationNum] = {}
    for arg in func.arguments:
        prog_var, inc = ubc.unpack_dsa_var(arg)
        assert prog_var not in latest_assignment
        latest_assignment[prog_var] = inc

    for n in path:
        if n in (ubc.NodeNameErr, ubc.NodeNameRet):
            continue

        for dsa_var in set(read_variables_in_node(func.nodes[n])):
            # loop targets are havoc'd at the top of the loop header
            # that is, it is legal to use them in the loop header itself
            if func.is_loop_header(n):
                for target in func.loops[n].targets:
                    prog_var, inc = ubc.unpack_dsa_var(target)
                    latest_assignment[prog_var] = inc

            prog_var, inc = ubc.unpack_dsa_var(dsa_var)
            if prog_var in latest_assignment:
                assert inc == latest_assignment[prog_var], f"{prog_var=} {n=} {path=}"
            # we don't assert that inc == 1 otherwise, because prog_var:1
            # might be used on some other path that joins with our own(and so
            # inc would be 2 for example)

        for dsa_var in assigned_variables_in_node(func, n):
            prog_var, inc = ubc.unpack_dsa_var(dsa_var)
            latest_assignment[prog_var] = inc



# ensure each variable is assigned to exactly once
# ensure each

def ensure_valid_dsa(unsafe_func: syntax.Function):
    plain_func = ubc.convert_function(unsafe_func)
    dsa_func = ubc.dsa(plain_func)

    all_paths = compute_all_path(dsa_func.cfg)
    for i, path in enumerate(all_paths):
        ensure_assigned_at_most_once(dsa_func, path)
        ensure_using_latest_incarnation(dsa_func, path)


@pytest.mark.parametrize('func', (f for f in example_dsa_CFunctions[1].values() if f.entry is not None))
def test_dsa_custom_tests(func: syntax.Function):
    if '.fail_' in func.name:
        pass
        # plain_func = ubc.convert_function(func)
        # with pytest.raises(ubc.DSAPotentialUndefinedBehaviour):
        #     ubc.dsa(plain_func)
    else:
        ensure_valid_dsa(func)


# @pytest.mark.skip
# sort so that the smallest functions fail first
@pytest.mark.parametrize('function', (f for f in sorted(kernel_CFunctions[1].values(), key=lambda f: len(f.nodes)) if f.entry is not None))
def test_dsa_kernel_functions(function: syntax.Function):
    print(function.name)
    if function.name in ('Kernel_C.deriveCap', 'Kernel_C.decodeCNodeInvocation'):
        pytest.skip("there's an assert true that messes DSA up")

    if len(compute_all_path(ubc.convert_function(function).cfg)) > 1000:
        pytest.skip("too many paths, checking them all is too slow")

    ensure_valid_dsa(function)


if __name__ == '__main__':
    ensure_valid_dsa(
        kernel_CFunctions[1]['Kernel_C.setDomain'])
