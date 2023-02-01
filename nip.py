"""
non-initialized protection

Guarantees that every variable that is used is initialized before-hand.

short circuiting: a && b won't evaluate b is a is true. So the statement

    prove a && b                                   ; should translate to
    prove (a_defined && (a || (b_defined && b)))   ; but for now we do
    prove a_defined && b_defined && a && b
"""

from dataclasses import dataclass
import dataclasses
from functools import reduce
import abc_cfg
from typing import Iterator, NewType, Sequence, TypeAlias, cast
from typing_extensions import assert_never
import source


@dataclass(frozen=True)
class Function(source.Function[source.ProgVarName]):
    """
    Non-initialized protected function
    """


GuardVarName = NewType('GuardVarName', str)
GuardVar = source.ExprVarT[GuardVarName]


@dataclass(frozen=True)
class NodeGuard(source.NodeCond[GuardVarName]):
    pass


@dataclass(frozen=True)
class NodeStateUpdate(source.NodeBasic[GuardVarName]):
    pass


Node: TypeAlias = NodeGuard | NodeStateUpdate


def guard_name(name: source.ProgVarName) -> GuardVarName:
    return GuardVarName(source.ProgVarName(f'{name}#init'))


def guard_var(var: source.ProgVar) -> GuardVar:
    return GuardVar(source.type_bool, guard_name(var.name))


def var_deps(expr: source.ExprT[source.ProgVarName]) -> source.ExprT[GuardVarName]:
    # for now, we ignore short circuiting
    # if a = b + c, returns a#init = b#init && c#init
    return reduce(source.expr_and, map(guard_var, source.all_vars_in_expr(expr)), source.expr_true)


def make_state_update_for_node(node: source.Node[source.ProgVarName]) -> Iterator[source.Update[GuardVarName]]:
    if isinstance(node, source.NodeBasic):
        for upd in node.upds:
            yield source.Update(guard_var(upd.var), var_deps(upd.expr))
    elif isinstance(node, source.NodeCall):
        deps = reduce(source.expr_and, (var_deps(arg)
                                        for arg in node.args), source.expr_true)
        for ret in node.rets:
            yield source.Update(guard_var(ret), deps)
    elif not isinstance(node, source.NodeEmpty | source.NodeCond):
        assert_never(node)


def make_protection_for_node(node: source.Node[source.ProgVarName]) -> source.ExprT[GuardVarName]:
    # for now, we ignore short circuiting
    return reduce(source.expr_and, map(guard_var, source.used_variables_in_node(node)), source.expr_true)


def make_initial_state(func: source.Function[source.ProgVarName]) -> Iterator[source.Update[GuardVarName]]:
    # TODO: globals
    for arg in func.arguments:
        yield source.Update(guard_var(arg), source.expr_true)


def update_node_successors(node: source.Node[source.VarNameKind], successors: Sequence[source.NodeName]) -> source.Node[source.VarNameKind]:
    if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeEmpty):
        assert len(successors) == 1, "wrong number of successors for node"
        return dataclasses.replace(node, succ=successors[0])

    if isinstance(node, source.NodeCond):
        assert len(successors) == 2, "wrong number of successors for node"
        return dataclasses.replace(node, succ_then=successors[0], succ_else=successors[1])

    assert_never(node)


def cast_guard_node_to_prog_node(expr: source.Node[GuardVarName]) -> source.Node[source.ProgVarName]:
    """
    Guard var names are used during to constructions to ensure we're indeed
    talking about <x>#init variables and not <x>

    But it breaks Liskov substitution principle because GuardVarName is a
    subtype of ProgVarName.

    TODO: how should the code be structured?
    """
    return cast(source.Node[source.ProgVarName], expr)


def nip(func: source.Function[source.ProgVarName]) -> Function:
    """
    - after the entry node, forall all arguments a, set <a>_initialized = true in a
      basic block.
    - for each original node in the graph:
        - NodeBasic | NodeCall | NodeCond
            - add predecessor: assert node for every expression used
        - NodeBasic | NodeCall
            - add successor: NodeBasic updating the _initialized variables
    """

    assert isinstance(func.nodes[func.cfg.entry],
                      source.NodeEmpty), "entry node should be a NodeEmpty"

    # predecessors, making sure that every used variable is defined
    protections: dict[source.NodeName, source.ExprT[GuardVarName]] = {}

    # successors, updating the initialized state after each node
    state_updates: dict[source.NodeName,
                        tuple[source.Update[GuardVarName], ...]] = {}

    state_updates[func.cfg.entry] = tuple(make_initial_state(func))

    for n in func.traverse_topologically():
        if n in (source.NodeNameErr, source.NodeNameRet):
            continue

        node = func.nodes[n]
        if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeCond):
            assert n not in protections
            p = make_protection_for_node(node)
            if p != source.expr_true:
                protections[n] = p
        elif not isinstance(node, source.NodeEmpty):
            assert_never(node)

        if isinstance(node, source.NodeBasic | source.NodeCall):
            assert n not in state_updates
            state_updates[n] = tuple(make_state_update_for_node(node))
        elif not isinstance(node, source.NodeEmpty | source.NodeCond):
            assert_never(node)

    # Before: Node1 ----------------------------------------------> Node2
    #                             becomes
    #     or: Node1 ----------------------------------------------> Node2
    #     or: Node1 -------------------------> Node2 protection --> Node2
    #     or: Node1 --> Node1 state update -----------------------> Node2
    #     or: Node1 --> Node1 state update --> Node2 protection --> Node2

    # apply insertions
    new_nodes: dict[source.NodeName, source.Node[source.ProgVarName]] = {}
    for n in func.traverse_topologically():
        if n in (source.NodeNameRet, source.NodeNameErr):
            continue

        node = func.nodes[n]
        jump_to = list(func.cfg.all_succs[n])

        # insert successor's predecessors
        for i, succ in enumerate(func.cfg.all_succs[n]):
            if succ in protections:
                # protection node for node succ, branch i
                protection_name = source.NodeName(f'guard_n{succ}')
                jump_to[i] = protection_name

                if protection_name in new_nodes:
                    # if a node has multiple predecessors, then they are all
                    # going to try to insert its predecessor. But only one
                    # should do it.
                    #
                    # but they should all jump to it regardless
                    assert len(func.cfg.all_preds[succ]) > 1
                    # assert False, f"{succ}"
                    continue

                assert protection_name not in new_nodes, protection_name
                new_nodes[protection_name] = cast_guard_node_to_prog_node(NodeGuard(
                    protections[succ], succ_then=succ, succ_else=source.NodeNameErr))

        # insert successors
        if n in state_updates:
            # we are lucky, if we have a state update, then we can only have
            # one successor because only NodeBasic and NodeCall have
            # successors
            assert isinstance(node, source.NodeBasic |
                              source.NodeCall | source.NodeEmpty), f"{type(node)}"
            assert len(jump_to) == 1
            update_name = source.NodeName(f'upd_n{n}')
            new_nodes[update_name] = cast_guard_node_to_prog_node(
                NodeStateUpdate(state_updates[n], jump_to[0]))
            jump_to[0] = update_name

        new_nodes[n] = update_node_successors(node, jump_to)

    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(new_nodes, cfg)
    return Function(cfg=cfg, nodes=new_nodes, loops=loops, arguments=func.arguments, name=func.name)
