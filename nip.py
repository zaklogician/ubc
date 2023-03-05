"""
non-initialized protection

Guarantees that every variable that is used is initialized before-hand.

short circuiting: a && b won't evaluate b is a is true. So the statement

    prove a && b                                   ; should translate to
    prove (a_defined && (a || (b_defined && b)))   ; but for now we do
    prove a_defined && b_defined && a && b
"""

from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
import dataclasses
from functools import reduce
import abc_cfg
from typing import Any, Callable, Iterator, Mapping, NewType, Sequence, Set, TypeAlias, overload
from typing_extensions import assert_never
import source


class GuardVarName(str):
    """ for example foo___int#v#assigned """


GuardVar = source.ExprVarT[GuardVarName]


@dataclass(frozen=True)
class GenericFunction(source.GenericFunction[source.VarNameKind, source.VarNameKind2]):
    """
    Non-initialized protected function
    """
    ghost: source.Ghost[source.VarNameKind2]


Function = GenericFunction[source.ProgVarName |
                           GuardVarName, source.ProgVarName | GuardVarName]


@dataclass(frozen=True)
class NodeGuard(source.NodeCond[GuardVarName]):
    pass


@dataclass(frozen=True)
class NodeStateUpdate(source.NodeBasic[GuardVarName]):
    pass


Node: TypeAlias = NodeGuard | NodeStateUpdate


def guard_name(name: source.ProgVarName) -> GuardVarName:
    return GuardVarName(source.ProgVarName(name + '#assigned'))


def guard_var(var: source.ProgVar) -> GuardVar:
    return GuardVar(source.type_bool, guard_name(var.name))


def var_deps(expr: source.ExprT[source.ProgVarName]) -> source.ExprT[GuardVarName]:
    # for now, we ignore short circuiting
    # if a = b + c, returns a#assigned = b#assigned && c#assigned
    return reduce(source.expr_and, map(guard_var, source.all_vars_in_expr(expr)), source.expr_true)


def make_state_update_for_node(node: source.Node[source.ProgVarName]) -> Iterator[source.Update[GuardVarName]]:
    if isinstance(node, source.NodeBasic):
        for upd in node.upds:
            if not source.is_loop_counter_name(upd.var.name):
                yield source.Update(guard_var(upd.var), var_deps(upd.expr))
    elif isinstance(node, source.NodeCall):
        deps = reduce(source.expr_and, (var_deps(arg)
                                        for arg in node.args), source.expr_true)
        for ret in node.rets:
            assert not source.is_loop_counter_name(
                ret.name), "didn't expect a return value to be a loop counter"
            yield source.Update(guard_var(ret), deps)
    else:
        assert not isinstance(node, source.NodeEmpty | source.NodeCond |
                              source.NodeAssume | source.NodeAssert), "doesn't make sense to have a state update for those nodes"
        assert_never(node)


def make_protection_for_node(node: source.Node[source.ProgVarName]) -> source.ExprT[GuardVarName]:
    # for now, we ignore short circuiting
    return reduce(source.expr_and, (guard_var(v) for v in source.used_variables_in_node(node) if not source.is_loop_counter_name(v.name)), source.expr_true)


def make_initial_state(func: source.Function) -> Iterator[source.Update[GuardVarName]]:
    # TODO: globals
    for arg in func.metadata.arguments:
        yield source.Update(guard_var(arg), source.expr_true)

    for other in func.all_variables() - set(func.metadata.arguments):
        yield source.Update(guard_var(other), source.expr_false)


def update_node_successors(node: source.Node[source.VarNameKind], successors: Sequence[source.NodeName]) -> source.Node[source.VarNameKind]:
    # FIXME: DANGER this successor ordering is pretty dangerous
    #        find a way to do this more safely.
    if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeEmpty | source.NodeAssume | source.NodeAssert):
        assert len(successors) == 1, "wrong number of successors for node"
        return dataclasses.replace(node, succ=successors[0])

    if isinstance(node, source.NodeCond):
        assert len(successors) == 2, "wrong number of successors for node"
        return dataclasses.replace(node, succ_then=successors[0], succ_else=successors[1])

    assert_never(node)


class UnificationError(Exception):
    pass


def unify_variables_to_make_ghost(func: source.Function) -> source.Ghost[source.ProgVarName | GuardVarName]:
    conversion_map: defaultdict[source.ExprVarT[source.HumanVarName],
                                list[source.ExprVarT[source.ProgVarName | GuardVarName]]] = defaultdict(lambda: [])

    # FIXME: make this more efficient if needed
    all_vars = func.all_variables()
    for var in all_vars:
        prefix = source.HumanVarNameSubject(var.name.split('___')[0])
        conversion_map[source.ExprVar(var.typ, source.HumanVarName(
            prefix, path=(), use_guard=False))].append(var)
        conversion_map[source.ExprVar(source.type_bool, source.HumanVarName(
            prefix, path=(), use_guard=True))].append(guard_var(var))

    # conversion_map[]

    def converter(human: source.ExprVarT[source.HumanVarName]) -> source.ExprVarT[source.ProgVarName | GuardVarName]:
        if human not in conversion_map:
            raise UnificationError(f"no variable matched with {human}")

        if len(conversion_map[human]) > 1:
            raise UnificationError(
                f"ambiguous name {human}, matches with all of {conversion_map[human]}")

        match = conversion_map[human][0]
        if human.typ != match.typ:
            raise UnificationError(
                f"matched variable doesn't have equal type: {human} {match}")

        return match

    def postcondition_converter(human: source.ExprVarT[source.HumanVarName]) -> source.ExprVarT[source.ProgVarName | GuardVarName]:
        if human.name.subject is source.HumanVarNameSpecial.RET:
            assert len(human.name.path) == 0, "path aren't supported yet"
            ret = func.c_return(human.name.path)
            # TODO: better error reporting mechanism
            if ret is None:
                raise ValueError(
                    "UserError: post condition used return value but functions has return type void")
            return ret

        return converter(human)

    return source.Ghost(
        precondition=source.convert_expr_vars(
            converter, func.ghost.precondition),
        postcondition=source.convert_expr_vars(
            postcondition_converter, func.ghost.postcondition),
        loop_invariants={lh: source.convert_expr_vars(converter, inv) for lh, inv in func.ghost.loop_invariants.items()})


def nip(func: source.Function) -> Function:
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

    for n in func.traverse_topologically(skip_err_and_ret=True):
        node = func.nodes[n]
        if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeCond):
            assert n not in protections
            p = make_protection_for_node(node)
            if p != source.expr_true:
                protections[n] = p
        elif isinstance(node, source.NodeAssume | source.NodeAssert):
            # TODO(nice to have): we could make this type safe
            assert False, "didn't expect to see node assume during this stage"
        elif not isinstance(node, source.NodeEmpty):
            assert_never(node)

        if isinstance(node, source.NodeBasic | source.NodeCall):
            assert n not in state_updates
            upds = tuple(make_state_update_for_node(node))
            if len(upds) > 0:
                state_updates[n] = upds
        elif not isinstance(node, source.NodeEmpty | source.NodeCond):
            assert_never(node)

    # Before: Node1 ----------------------------------------------> Node2
    #                             becomes
    #     or: Node1 ----------------------------------------------> Node2
    #     or: Node1 -------------------------> Node2 protection --> Node2
    #     or: Node1 --> Node1 state update -----------------------> Node2
    #     or: Node1 --> Node1 state update --> Node2 protection --> Node2

    # apply insertions
    new_nodes: dict[source.NodeName,
                    source.Node[source.ProgVarName | GuardVarName]] = {}
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
                new_nodes[protection_name] = NodeGuard(
                    protections[succ], succ_then=succ, succ_else=source.NodeNameErr)

        # insert successors
        if n in state_updates:
            # we are lucky, if we have a state update, then we can only have
            # one successor because only NodeBasic and NodeCall have
            # successors
            assert isinstance(node, source.NodeBasic |
                              source.NodeCall | source.NodeEmpty), f"{type(node)}"
            assert len(jump_to) == 1
            update_name = source.NodeName(f'upd_n{n}')
            new_nodes[update_name] = NodeStateUpdate(
                state_updates[n], jump_to[0])
            jump_to[0] = update_name

        new_nodes[n] = update_node_successors(node, jump_to)

    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)

    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    return Function(cfg=cfg, nodes=new_nodes, loops=loops, metadata=func.metadata,
                    name=func.name, ghost=unify_variables_to_make_ghost(func))
