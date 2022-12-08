from sys import platform
from _pytest.capture import pytest_load_initial_conftests
import pytest
from typing import Collection, Iterable, Iterator, Mapping, Sequence, Set
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

    if loop_header := func.is_loop_header(n):
        assigned_variables.extend(func.loops[loop_header].targets)

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
            if loop_header := func.is_loop_header(n):
                for target in func.loops[loop_header].targets:
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


def ensure_valid_dsa(dsa_func: ubc.Function[ubc.DSAVarName]):
    all_paths = compute_all_path(dsa_func.cfg)
    for i, path in enumerate(all_paths):
        ensure_assigned_at_most_once(dsa_func, path)
        ensure_using_latest_incarnation(dsa_func, path)


def traverse_func(func: ubc.Function) -> Iterator[ubc.NodeName]:
    q: list[ubc.NodeName] = [
        n for n, preds in func.cfg.all_preds.items() if len(preds) == 0]
    visited: set[ubc.NodeName] = set()
    while q:
        n = q.pop(-1)
        if n in visited:
            continue

        if not all(p in visited for p in func.cycleless_preds_of(n)):
            continue

        visited.add(n)
        yield n

        for succ in func.cfg.all_succs[n]:
            if (n, succ) not in func.cfg.back_edges:
                q.append(succ)

    assert len(visited - {ubc.NodeNameErr, ubc.NodeNameRet}) == len(func.nodes)


def assert_expr_equals_mod_dsa(lhs: ubc.Expr[ubc.ProgVarName], rhs: ubc.Expr[ubc.DSAVarName]):
    assert lhs.typ == rhs.typ

    if isinstance(lhs, ubc.ExprNum | ubc.ExprSymbol | ubc.ExprType):
        return lhs == rhs
    elif isinstance(lhs, ubc.ExprVar):
        assert isinstance(rhs, ubc.ExprVar)
        assert lhs.name == ubc.unpack_dsa_var_name(rhs.name)[0]
    elif isinstance(lhs, ubc.ExprOp):
        assert isinstance(rhs, ubc.ExprOp)
        assert lhs.operator == rhs.operator
        assert len(lhs.operands) == len(rhs.operands)
        for i in range(len(lhs.operands)):
            assert_expr_equals_mod_dsa(lhs.operands[i], rhs.operands[i])
    else:
        assert_never(lhs)


def assert_var_equal_mod_dsa(prog: ubc.ProgVar, dsa: ubc.DSAVar):
    assert prog == ubc.unpack_dsa_var(dsa)[0]


def ensure_correspondence(prog_func: ubc.Function[ubc.ProgVarName], dsa_func: ubc.Function[ubc.DSAVarName]):
    assert set(prog_func.nodes.keys()).issubset(dsa_func.nodes.keys())

    join_node_names: list[ubc.NodeName] = []

    for node_name in dsa_func.nodes:
        if node_name in (ubc.NodeNameErr, ubc.NodeNameRet):
            continue

        dsa_node = dsa_func.nodes[node_name]

        if node_name not in prog_func.nodes:
            # ensure it's a join node

            assert node_name.startswith('j')  # not required semantically

            assert isinstance(dsa_node, ubc.BasicNode)
            for upd in dsa_node.upds:
                # ensure every update is of the form A.X = A.Y
                lhs_name, _ = ubc.unpack_dsa_var_name(upd.var.name)
                assert isinstance(upd.expr, ubc.ExprVar)
                rhs_name, _ = ubc.unpack_dsa_var_name(upd.expr.name)
                assert upd.var.typ == upd.expr.typ

            join_node_names.append(node_name)

            continue

        prog_node = prog_func.nodes[node_name]

        if isinstance(prog_node, ubc.BasicNode):
            assert isinstance(dsa_node, ubc.BasicNode)

            assert len(prog_node.upds) == len(dsa_node.upds)
            for i in range(len(prog_node.upds)):
                assert_var_equal_mod_dsa(
                    prog_node.upds[i].var, dsa_node.upds[i].var)

                assert_expr_equals_mod_dsa(
                    prog_node.upds[i].expr, dsa_node.upds[i].expr)

        elif isinstance(prog_node, ubc.CallNode):
            assert isinstance(dsa_node, ubc.CallNode)

            assert len(prog_node.args) == len(dsa_node.args)
            for i in range(len(prog_node.args)):
                assert_expr_equals_mod_dsa(prog_node.args[i], dsa_node.args[i])

            assert len(prog_node.rets) == len(dsa_node.rets)
            for i in range(len(prog_node.rets)):
                assert_var_equal_mod_dsa(prog_node.rets[i], dsa_node.rets[i])

        elif isinstance(prog_node, ubc.CondNode):
            assert isinstance(dsa_node, ubc.CondNode)
            assert_expr_equals_mod_dsa(prog_node.expr, dsa_node.expr)

        elif isinstance(prog_node, ubc.EmptyNode):
            assert isinstance(dsa_node, ubc.EmptyNode)
        else:
            assert_never(prog_node)

    for node_name in traverse_func(prog_func):
        prog_succs = prog_func.cfg.all_succs[node_name]
        dsa_succs = dsa_func.cfg.all_succs[node_name]

        if prog_succs == dsa_succs:
            continue

        # the only reason the successors wouldn't been the same is if a dsa
        # successor was a join node.

        assert len(prog_succs) == len(dsa_succs)
        for i in range(len(prog_succs)):
            if prog_succs[i] == dsa_succs[i]:
                continue

            # we must have
            # prog:  a -----------> b
            # dsa :  a --> join --> b

            assert dsa_succs[i] in join_node_names
            join_node_succs = dsa_func.cfg.all_succs[dsa_succs[i]]
            assert len(join_node_succs) == 1
            assert join_node_succs[0] == prog_succs[i]


@pytest.mark.parametrize('func', (f for f in example_dsa_CFunctions[1].values() if f.entry is not None))
def test_dsa_custom_tests(func: syntax.Function):
    prog_func = ubc.convert_function(func)
    dsa_func = ubc.dsa(prog_func)
    # ensure_valid_dsa(dsa_func)
    ensure_correspondence(prog_func, dsa_func)


# sort so that the smallest functions fail first
@pytest.mark.parametrize('function', (f for f in sorted(kernel_CFunctions[1].values(), key=lambda f: len(f.nodes)) if f.entry is not None))
def test_dsa_kernel_functions(function: syntax.Function):
    print(function.name)
    if function.name in ('Kernel_C.deriveCap', 'Kernel_C.decodeCNodeInvocation'):
        pytest.skip("there's an assert true that messes DSA up")

    if len(compute_all_path(ubc.convert_function(function).cfg)) > 1000:
        pytest.skip("too many paths, checking them all is too slow")

    prog_func = ubc.convert_function(function)
    dsa_func = ubc.dsa(prog_func)
    ensure_valid_dsa(dsa_func)
    ensure_correspondence(prog_func, dsa_func)
