from typing import Set, get_args
from typing_extensions import assert_never
import pytest
import source
import nip


import syntax

# global variables are bad :(
syntax.set_arch('rv64')


with open('examples/kernel_CFunctions.txt') as f:
    kernel_CFunctions = syntax.parse_and_install_all(
        f, None)

with open('tests/all.txt') as f:
    example_test_CFunctions = syntax.parse_and_install_all(f, None)
del f


def non_nip_successors(nip_func: nip.Function, n: source.NodeName) -> Set[source.NodeName]:
    non_nip_succs: set[source.NodeName] = set()

    q: set[source.NodeName] = set()
    for succ in nip_func.cfg.all_succs[n]:
        q.add(succ)

    while len(q) > 0:
        n = q.pop()
        if n in (source.NodeNameErr, source.NodeNameRet):
            non_nip_succs.add(n)
            continue

        node = nip_func.nodes[n]
        if isinstance(node, nip.NodeStateUpdate):
            q.add(node.succ)
        elif isinstance(node, nip.NodeGuard):
            q.add(node.succ_then)
        else:
            non_nip_succs.add(n)

    return non_nip_succs


def ensure_node_equals_mod_nip(lhs: source.Node[source.ProgVarName], rhs: source.Node[source.ProgVarName]) -> None:
    if isinstance(lhs, source.NodeBasic):
        assert isinstance(rhs, source.NodeBasic)
        assert lhs.upds == rhs.upds
    elif isinstance(lhs, source.NodeCond):
        assert isinstance(rhs, source.NodeCond)
        assert lhs.expr == rhs.expr
    elif isinstance(lhs, source.NodeCall):
        assert isinstance(rhs, source.NodeCall)
        assert lhs.args == rhs.args
        assert lhs.rets == rhs.rets
        assert lhs.fname == rhs.fname
    elif isinstance(lhs, source.NodeEmpty):
        assert isinstance(rhs, source.NodeEmpty)
    else:
        assert_never(lhs)


def skip_nip_nodes(func: nip.Function, n: source.NodeName) -> source.NodeName:
    if n in (source.NodeNameErr, source.NodeNameRet):
        return n

    node = func.nodes[n]
    if isinstance(node, nip.NodeStateUpdate):
        return skip_nip_nodes(func, node.succ)

    if isinstance(node, nip.NodeGuard):
        return skip_nip_nodes(func, node.succ_then)

    return n


def ensure_correspondence(prog_func: source.Function[source.ProgVarName], nip_func: nip.Function) -> None:
    """
    Ignoring the nip nodes, the cfgs should be the exact same
    """

    num_nip_nodes = 0
    for n in nip_func.nodes:
        if n in (source.NodeNameErr, source.NodeNameRet):
            continue

        nip_node = nip_func.nodes[n]
        if isinstance(nip_node, nip.NodeStateUpdate | nip.NodeGuard):
            num_nip_nodes += 1
            continue

        prog_node = prog_func.nodes[n]
        ensure_node_equals_mod_nip(nip_func.nodes[n], prog_func.nodes[n])

        if isinstance(nip_node, source.NodeBasic | source.NodeEmpty | source.NodeCall):
            assert isinstance(prog_node, source.NodeBasic |
                              source.NodeEmpty | source.NodeCall)
            assert skip_nip_nodes(nip_func, nip_node.succ) == prog_node.succ
        elif isinstance(nip_node, source.NodeCond):
            assert isinstance(prog_node, source.NodeCond)
            assert skip_nip_nodes(
                nip_func, nip_node.succ_then) == prog_node.succ_then
            assert skip_nip_nodes(
                nip_func, nip_node.succ_else) == prog_node.succ_else
        else:
            assert_never(nip_node)

    assert len(prog_func.nodes) + num_nip_nodes == len(nip_func.nodes)


def ensure_guard_and_state_update_correctness(nip_func: nip.Function) -> None:
    for n in nip_func.traverse_topologically():
        if n in (source.NodeNameRet, source.NodeNameErr):
            continue

        node = nip_func.nodes[n]
        if isinstance(node, get_args(nip.Node)):
            continue

        used_variables = source.used_variables_in_node(node)
        if len(used_variables) > 0:
            preds = nip_func.cfg.all_preds[n]
            assert len(preds) == 1, f'{n=} {preds=}'
            guard = nip_func.nodes[preds[0]]
            assert isinstance(guard, nip.NodeGuard)
            assert guard.succ_else == source.NodeNameErr
            assert guard.succ_then == n

            # easy because we don't do any short-circuiting
            assert set(source.expr_split_conjuncts(guard.expr)) == set(
                map(nip.guard_var, used_variables))

        assigned_variables = source.assigned_variables_in_node(
            nip_func, n, with_loop_targets=False)
        if len(assigned_variables) > 0:
            succs = nip_func.cfg.all_succs[n]
            assert len(succs) == 1, f'{n=} {succs=}'
            upd_node = nip_func.nodes[succs[0]]
            assert isinstance(upd_node, nip.NodeStateUpdate)

            assert set(upd.var for upd in upd_node.upds) == set(
                map(nip.guard_var, assigned_variables))
            # TODO: make sure the dependencies are correct. Not much value in
            # doing that because I'm repeating the exact same logic that's in
            # the code already


def do_nip_test(func: syntax.Function) -> None:
    print(func.name)
    prog_func = source.convert_function(func)
    nip_func = nip.nip(prog_func)
    ensure_correspondence(prog_func, nip_func)
    ensure_guard_and_state_update_correctness(nip_func)


@pytest.mark.parametrize('func', (f for f in example_test_CFunctions[1].values() if f.entry is not None))
def test_nip_test_functions(func: syntax.Function) -> None:
    do_nip_test(func)


@pytest.mark.parametrize('func', (f for f in sorted(kernel_CFunctions[1].values(), key=lambda f: len(f.nodes)) if f.entry is not None))
def test_nip_kernel_functions(func: syntax.Function) -> None:
    do_nip_test(func)
