"""
unify_var(h: HumanVar): ProgVar


insert_precondition(p: Expr[HumanVarName])
    after the entry node, insert PreconditionAssumption
insert_postcondition()
    before the ret node, insert a PostConditionProofObligation
insert_loop_invariant()
    for every lh := loop header
        for every p := pred(lh)
            insert NodeLoopInvariantProofObligation between p-lh
        insert NodeLoopInvariantAssumption
"""


from dataclasses import dataclass
import dataclasses
from enum import Enum, unique
from typing import Callable, Iterable, Mapping, NamedTuple, Sequence, Tuple, Any, Iterator, Dict
from typing_extensions import assert_never
import abc_cfg
import source
import nip
from collections import defaultdict
import ghost_data as gd
import syntax


@dataclass(frozen=True)
class NodePostConditionProofObligation(source.NodeCond[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodePreconditionAssumption(source.NodeAssume[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeLoopInvariantAssumption(source.NodeAssume[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeLoopInvariantProofObligation(source.NodeCond[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodePrecondObligationFnCall(source.NodeAssert[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeAssumePostCondFnCall(source.NodeAssume[source.VarNameKind]):
    pass


NodeGhostCode = (NodePostConditionProofObligation[source.VarNameKind]
                 | NodePreconditionAssumption[source.VarNameKind]
                 | NodeLoopInvariantAssumption[source.VarNameKind]
                 | NodeLoopInvariantProofObligation[source.VarNameKind]
                 | NodePrecondObligationFnCall
                 | NodeAssumePostCondFnCall)


class GenericFunction(nip.GenericFunction[source.VarNameKind, source.VarNameKind2]):
    """
    Function pre conditions, post condition, and loop invariants inserted in
    the CFG
    """


Function = GenericFunction[source.ProgVarName |
                           nip.GuardVarName, source.ProgVarName | nip.GuardVarName]


@unique
class K(Enum):
    """ Only used in this module, hence the short name """

    POST_CONDITION_PROOF_OBLIGATION = NodePostConditionProofObligation
    PRECONDITION_ASSUMPTION = NodePreconditionAssumption
    NODE_LOOP_INVARIANT_ASSUMPTION = NodeLoopInvariantAssumption
    NODE_LOOP_INVARIANT_PROOF_OBLIGATION = NodeLoopInvariantProofObligation
    NODE_PRE_CONDITION_OBLIGATION_FNCALL = NodePrecondObligationFnCall
    NODE_ASSUME_POST_CONDITION_FNCALL = NodeAssumePostCondFnCall


class Insertion(NamedTuple):
    after: source.NodeName
    before: source.NodeName
    kind: K
    expr: source.ExprT[source.ProgVarName | nip.GuardVarName]
    node_name: source.NodeName


class InsertionCommon(NamedTuple):
    before: source.NodeName
    expr: source.ExprT[source.ProgVarName | nip.GuardVarName]


def no_insertion_on_same_edge(insertions: Sequence[Insertion]) -> bool:
    edges = tuple((ins.after, ins.before) for ins in insertions)
    return len(edges) == len(set(edges))


def insert_single_succ_node_on_edge(
        nodes: dict[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]],
        after_name: source.NodeName,
        before_name: source.NodeName,
        constructor: Callable[[source.NodeName], tuple[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]]]) -> None:
    """
    constructor :: NodeName -> (NodeName, Node)
    constructor "name of new node successor" -> (name of new node, new node)

    modifies 'nodes' in place
    """

    # after  ----->   new node  ----->  before
    #        ^                  ^ edge 2
    #        | edge 1

    assert after_name in nodes, f'inserting after imaginary node'
    assert before_name in nodes or before_name in (
        source.NodeNameErr, source.NodeNameRet), f'inserting before imaginary node'

    # make the node and edge 2 at the same time
    new_node_name, new_node = constructor(before_name)
    assert new_node_name not in nodes, f'new node name is already taken {new_node_name}'
    nodes[new_node_name] = new_node

    # make edge 1
    after = nodes[after_name]
    if isinstance(after, source.NodeEmpty | source.NodeAssume | source.NodeBasic | source.NodeCall | source.NodeAssert):
        # just for type safety (dataclasses.replace isn't type checked)
        after.succ
        nodes[after_name] = dataclasses.replace(after, succ=new_node_name)
    elif isinstance(after, source.NodeCond):
        if after.succ_then == before_name:
            nodes[after_name] = dataclasses.replace(
                after, succ_then=new_node_name)
        elif after.succ_else == before_name:
            nodes[after_name] = dataclasses.replace(
                after, succ_else=new_node_name)
        else:
            assert False, "that must mean that the edge isn't valid"
    else:
        assert_never(after)


def apply_insertions(func: nip.Function, insertions: Sequence[Insertion]) -> Mapping[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]]:

    # Inserting multiple nodes on the same edge ie.
    #
    #   [insert (after=a, before=b, ...), insert(after=a, before=b, ...), ...]
    #
    # makes the graph modification a little bit more complicated. From my
    # observations, it seems like it can never occur.
    assert no_insertion_on_same_edge(
        insertions), ("not to worry, just need to handle inserting multiple nodes on the same edge. "
                      "Pay close attention of the intended order of the inserted nodes")

    def make_constructor(ins: Insertion) -> Callable[[source.NodeName], tuple[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]]]:
        def constructor(succ: source.NodeName) -> tuple[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]]:
            # the value of kind of class of the node
            if ins.kind is K.POST_CONDITION_PROOF_OBLIGATION:
                return ins.node_name, NodePostConditionProofObligation(ins.expr, succ_then=succ, succ_else=source.NodeNameErr)

            if ins.kind is K.PRECONDITION_ASSUMPTION:
                return ins.node_name, NodePreconditionAssumption(ins.expr, succ)

            if ins.kind is K.NODE_LOOP_INVARIANT_ASSUMPTION:
                return ins.node_name, NodeLoopInvariantAssumption(ins.expr, succ)

            if ins.kind is K.NODE_LOOP_INVARIANT_PROOF_OBLIGATION:
                return ins.node_name, NodeLoopInvariantProofObligation(ins.expr, succ_then=succ, succ_else=source.NodeNameErr)

            if ins.kind is K.NODE_PRE_CONDITION_OBLIGATION_FNCALL:
                return ins.node_name, NodePrecondObligationFnCall(ins.expr, succ)

            if ins.kind is K.NODE_ASSUME_POST_CONDITION_FNCALL:
                return ins.node_name, NodeAssumePostCondFnCall(ins.expr, succ)

            assert_never(ins.kind)

        return constructor

    new_nodes = dict(func.nodes)
    for ins in insertions:
        insert_single_succ_node_on_edge(
            new_nodes, ins.after, ins.before, make_constructor(ins))

    return new_nodes


def sprinkle_precondition(func: nip.Function) -> Iterable[Insertion]:
    entry_node = func.nodes[func.cfg.entry]
    assert isinstance(entry_node, source.NodeEmpty)

    yield Insertion(node_name=source.NodeName('pre_condition'),
                    after=func.cfg.entry,
                    before=entry_node.succ,
                    kind=K.PRECONDITION_ASSUMPTION,
                    expr=func.ghost.precondition)


def sprinkle_postcondition(func: nip.Function) -> Iterable[Insertion]:
    assert len(func.cfg.all_preds[source.NodeNameRet]) == 1, ("not to worry, just need to handle the case "
                                                              "where the Err node has multiple predecessors")
    pred = func.cfg.all_preds[source.NodeNameRet][0]
    yield Insertion(node_name=source.NodeName('post_condition'),
                    after=pred,
                    before=source.NodeNameRet,
                    kind=K.POST_CONDITION_PROOF_OBLIGATION,
                    expr=func.ghost.postcondition)


def sprinkle_loop_invariant(func: nip.Function, lh: source.LoopHeaderName) -> Iterable[Insertion]:
    # TODO
    # ----
    #
    # to generate more readable SMT, we should put the loop invariant into an
    # SMT function. It would be safe to also provide a proof that this
    # function only needs to have for parameter the loop targets.
    #
    # proof sketch: suppose the loop invariant depends on a variable which
    # isn't a loop target. By definition of loop targets, it is never on the
    # lhs of an assignment within the loop, thus it's value is constant, and
    # hence doesn't need to be a parameter. By exhaustion of cases, the
    # invariant's parameters only need to be the loop targets.
    #
    # If a variable isn't a loop target, the incarnation number to use is the
    # one that occurs in the loop header's DSA context (ie. the only incarnation
    # for that variable throughout the loop)

    # ALL predecessors, including predecessors that follow a back edge
    for i, pred in enumerate(func.cfg.all_preds[lh], start=1):
        yield Insertion(node_name=source.NodeName(f'loop_{lh}_latch_{i}'),
                        after=pred,
                        before=lh,
                        kind=K.NODE_LOOP_INVARIANT_PROOF_OBLIGATION,
                        expr=func.ghost.loop_invariants[lh])

    for i, succ in enumerate(func.cfg.all_succs[lh], start=1):
        yield Insertion(node_name=source.NodeName(f'loop_{lh}_inv_asm_{i}'),
                        after=lh,
                        before=succ,
                        kind=K.NODE_LOOP_INVARIANT_ASSUMPTION,
                        expr=func.ghost.loop_invariants[lh])


def sprinkle_loop_invariants(func: nip.Function) -> Iterable[Insertion]:
    for loop_header in func.loops:
        yield from sprinkle_loop_invariant(func, loop_header)


def sprinkle_call_assert_preconditions(fn: nip.Function, name: source.NodeName, precond: source.ExprT[source.ProgVarName | nip.GuardVarName]) -> Iterable[Insertion]:
    for pred in fn.cfg.all_preds[name]:
        yield Insertion(node_name=source.NodeName(f"assert_precond_{pred}_{name}"), after=pred, before=name, kind=K.NODE_PRE_CONDITION_OBLIGATION_FNCALL, expr=precond)


def sprinkle_call_assume_postcondition(name: source.NodeName, node: source.NodeCall[Any], postcond: source.ExprT[source.ProgVarName | nip.GuardVarName]) -> Insertion:
    return Insertion(node_name=source.NodeName(f"assume_postcond_{name}_{node.succ}"), after=name, before=node.succ, kind=K.NODE_ASSUME_POST_CONDITION_FNCALL, expr=postcond)


def get_call_nodes(fn: nip.Function) -> list[Tuple[source.NodeName, source.NodeCall[source.ProgVarName | nip.GuardVarName]]]:
    nodes: list[Tuple[source.NodeName,
                      source.NodeCall[source.ProgVarName | nip.GuardVarName]]] = []
    for (name, node) in fn.nodes.items():
        if isinstance(node, source.NodeCall):
            nodes.append((name, node))
    return nodes


def replace_vars(f: Callable[[source.ExprVarT[source.VarNameKind]], source.ExprT[source.VarNameKind2]], expr: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind2]:
    """replace each variable with an expression"""
    if isinstance(expr, source.ExprNum):
        return expr
    elif isinstance(expr, source.ExprVar):
        return f(expr)
    elif isinstance(expr, source.ExprOp):
        ops = tuple(replace_vars(f, operand) for operand in expr.operands)
        return source.ExprOp(expr.typ, source.Operator(expr.operator), operands=ops)
    elif isinstance(expr, source.ExprType | source.ExprSymbol):
        return expr
    elif isinstance(expr, source.ExprFunction):
        args = tuple(replace_vars(f, arg) for arg in expr.arguments)
        return source.ExprFunction(expr.typ, expr.function_name, args)
    return NotImplemented


def unify_preconds(raw_precondition: source.ExprT[source.HumanVarName], args: Tuple[source.ExprT[source.VarNameKind], ...], expected_args: Tuple[source.ExprVarT[source.ProgVarName], ...]) -> Tuple[Dict[source.ExprVarT[source.HumanVarName], source.ExprT[source.VarNameKind]], source.ExprT[source.VarNameKind]]:
    conversion_map: Dict[source.ExprVarT[source.HumanVarName],
                         source.ExprT[source.VarNameKind]] = {}

    assert len(expected_args) == len(args)

    for garg, earg in zip(args, expected_args):
        assert garg.typ == earg.typ
        conversion_map[source.ExprVar(earg.typ, source.HumanVarName(
            source.HumanVarNameSubject(earg.name), path=(), use_guard=False))] = garg

    def f(v: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.VarNameKind]:
        return conversion_map[v]
    return (conversion_map, replace_vars(f, raw_precondition))


def unify_postconds(raw_postcondition: source.ExprT[source.HumanVarName],
                    rets: Tuple[source.ExprT[source.VarNameKind], ...], expected_rets: Tuple[source.ExprVarT[source.ProgVarName], ...],
                    conversion_map: Dict[source.ExprVarT[source.HumanVarName], source.ExprT[source.VarNameKind]]) -> source.ExprT[source.VarNameKind]:
    assert len(rets) == len(expected_rets)
    for gret, eret in zip(rets, expected_rets):
        name = source.HumanVarName(source.HumanVarNameSubject(
            eret.name), path=(), use_guard=False)
        conversion_map[source.ExprVar(eret.typ, name)] = gret

    def f(v: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.VarNameKind]:
        return conversion_map[v]

    return replace_vars(f, raw_postcondition)


def sprinkle_call_conditions(filename: str, fn: nip.Function, ctx: Dict[str, source.FunctionMetadata[source.ProgVarName]]) -> Iterator[Insertion]:
    nodes = get_call_nodes(fn)
    for (name, node) in nodes:
        ghost = gd.get(filename, node.fname)
        # asserting True and assuming True is basically doing nothing
        raw_precondition = source.expr_true if ghost is None else ghost.precondition
        raw_postcondition = source.expr_true if ghost is None else ghost.postcondition
        call_target = ctx[node.fname]
        assert call_target is not None
        conversion_map, precondition = unify_preconds(
            raw_precondition, node.args, call_target.arguments)
        postcondition = unify_postconds(
            raw_postcondition, node.rets, call_target.returns, conversion_map)
        yield from sprinkle_call_assert_preconditions(fn, name, precondition)
        yield sprinkle_call_assume_postcondition(name, node, postcondition)

# sprinkle isn't the most trustworthy sounding word, but it's the most
# descriptive one I could think of


def sprinkle_ghost_code(filename: str, func: nip.Function, ctx: Dict[str, syntax.Function]) -> Function:
    new_ctx: dict[str, source.FunctionMetadata[source.ProgVarName]] = {}
    for fname, syn_func in ctx.items():
        new_ctx[fname] = source.convert_function_metadata(syn_func)
    insertions: list[Insertion] = []
    insertions.extend(sprinkle_precondition(func))
    insertions.extend(sprinkle_postcondition(func))
    insertions.extend(sprinkle_loop_invariants(func))
    insertions.extend(sprinkle_call_conditions(filename, func, new_ctx))
    new_nodes = apply_insertions(func, insertions)
    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    # new_nodes = search_common_succs(func, cfg)

    return Function(name=func.name, nodes=new_nodes, cfg=cfg, loops=loops, ghost=func.ghost, metadata=func.metadata)
