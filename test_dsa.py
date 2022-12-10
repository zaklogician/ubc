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

        path_so_far = list(all_paths[-1])
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


def ensure_assigned_at_most_once(func: ubc.Function[ubc.DSAVarName], path: Collection[ubc.NodeName]):
    assigned_variables: list[ubc.DSAVar] = []
    for node in path:
        assigned_variables.extend(ubc.assigned_variables_in_node(func, node))
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

        for dsa_var in ubc.used_variables_in_node(func.nodes[n]):
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

        for dsa_var in ubc.assigned_variables_in_node(func, n):
            prog_var, inc = ubc.unpack_dsa_var(dsa_var)
            latest_assignment[prog_var] = inc


def ensure_valid_dsa(dsa_func: ubc.Function[ubc.DSAVarName]):
    all_paths = compute_all_path(dsa_func.cfg)
    for i, path in enumerate(all_paths):
        ensure_assigned_at_most_once(dsa_func, path)
        ensure_using_latest_incarnation(dsa_func, path)


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


def assert_var_equals_mod_dsa(prog: ubc.ProgVar, dsa: ubc.DSAVar):
    assert prog == ubc.unpack_dsa_var(dsa)[0]


def assert_node_equals_mod_dsa(prog: ubc.Node[ubc.ProgVarName], dsa: ubc.Node[ubc.DSAVarName]):
    if isinstance(prog, ubc.NodeBasic):
        assert isinstance(dsa, ubc.NodeBasic)

        assert len(prog.upds) == len(dsa.upds)
        for i in range(len(prog.upds)):
            assert_var_equals_mod_dsa(
                prog.upds[i].var, dsa.upds[i].var)

            assert_expr_equals_mod_dsa(
                prog.upds[i].expr, dsa.upds[i].expr)

    elif isinstance(prog, ubc.NodeCall):
        assert isinstance(dsa, ubc.NodeCall)

        assert len(prog.args) == len(dsa.args)
        for i in range(len(prog.args)):
            assert_expr_equals_mod_dsa(prog.args[i], dsa.args[i])

        assert len(prog.rets) == len(dsa.rets)
        for i in range(len(prog.rets)):
            assert_var_equals_mod_dsa(prog.rets[i], dsa.rets[i])

    elif isinstance(prog, ubc.NodeCond):
        assert isinstance(dsa, ubc.NodeCond)
        assert_expr_equals_mod_dsa(prog.expr, dsa.expr)

    elif isinstance(prog, ubc.NodeEmpty):
        assert isinstance(dsa, ubc.NodeEmpty)
    else:
        assert_never(prog)


def assert_is_join_node(node: ubc.Node[ubc.DSAVarName]):

    assert isinstance(node, ubc.NodeBasic)
    for upd in node.upds:
        # ensure every update is of the form A.X = A.Y
        lhs_name, _ = ubc.unpack_dsa_var_name(upd.var.name)
        assert isinstance(upd.expr, ubc.ExprVar)
        rhs_name, _ = ubc.unpack_dsa_var_name(upd.expr.name)
        assert upd.var.typ == upd.expr.typ


def ensure_correspondence(prog_func: ubc.Function[ubc.ProgVarName], dsa_func: ubc.Function[ubc.DSAVarName]):
    assert set(prog_func.nodes.keys()).issubset(dsa_func.nodes.keys())

    join_node_names: list[ubc.NodeName] = []

    for node_name in dsa_func.nodes:
        if node_name in (ubc.NodeNameErr, ubc.NodeNameRet):
            continue

        dsa_node = dsa_func.nodes[node_name]

        if node_name not in prog_func.nodes:
            assert_is_join_node(dsa_node)
            assert node_name.startswith('j')  # not required semantically
            join_node_names.append(node_name)
        else:
            prog_node = prog_func.nodes[node_name]
            assert_node_equals_mod_dsa(prog_node, dsa_node)

    for node_name in ubc.traverse_func_topologically(prog_func):
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
    ensure_valid_dsa(dsa_func)
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
