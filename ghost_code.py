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
from global_smt_variables import is_global_smt, PLATFORM_CONTEXT_BIT_SIZE
import source
import nip
import ghost_data
import syntax
from itertools import chain


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


@dataclass(frozen=True)
class NodeAssumePrecondForArb(source.NodeAssume[source.VarNameKind]):
    pass


NodeGhostCode = (NodePostConditionProofObligation[source.VarNameKind]
                 | NodePreconditionAssumption[source.VarNameKind]
                 | NodeLoopInvariantAssumption[source.VarNameKind]
                 | NodeLoopInvariantProofObligation[source.VarNameKind]
                 | NodePrecondObligationFnCall[source.VarNameKind]
                 | NodeAssumePostCondFnCall[source.VarNameKind])


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
    NODE_ASSUME_PRECOND_FOR_ARB = NodeAssumePrecondForArb


class Insertion(NamedTuple):
    after: source.NodeName
    before: source.NodeName
    kind: K
    expr: source.ExprT[source.ProgVarName | nip.GuardVarName]
    node_name: source.NodeName


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

            if ins.kind is K.NODE_ASSUME_PRECOND_FOR_ARB:
                return ins.node_name, NodeAssumePrecondForArb(ins.expr, succ)

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
    #assert len(func.cfg.all_preds[source.NodeNameRet]) == 1, ("not to worry, just need to handle the case "
    #                                                          "where the Err node has multiple predecessors")
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


def sprinkle_call_assert_preconditions(fn: nip.Function, name: source.NodeName, precond: source.ExprT[source.ProgVarName | nip.GuardVarName], assume_cond: source.ExprT[source.ProgVarName | nip.GuardVarName] | None) -> Tuple[Iterable[Insertion], Iterable[Insertion]]:
    run_one: list[Insertion] = []
    run_two: list[Insertion] = []
    for pred in fn.cfg.all_preds[name]:
        assum_node_name = source.NodeName(f"assume_pre_{pred}_{name}")
        assert_node_name = source.NodeName(f"prove_{pred}_{name}")
        run_one.append(
            Insertion(node_name=assert_node_name, after=pred, before=name,
                      kind=K.NODE_PRE_CONDITION_OBLIGATION_FNCALL, expr=precond)
        )
        if assume_cond is not None:

            run_two.append(
                Insertion(node_name=assum_node_name, after=pred, before=assert_node_name,
                          kind=K.NODE_ASSUME_PRECOND_FOR_ARB, expr=assume_cond)
            )

    return iter(run_one), iter(run_two)


def sprinkle_call_assume_postcondition(name: source.NodeName, node: source.NodeCall[Any], postcond: source.ExprT[source.ProgVarName | nip.GuardVarName]) -> Insertion:
    return Insertion(node_name=source.NodeName(f"assume_postcond_{name}_{node.succ}"), after=name, before=node.succ, kind=K.NODE_ASSUME_POST_CONDITION_FNCALL, expr=postcond)


def unify_preconds(raw_precondition: source.ExprT[source.HumanVarName], args: Tuple[source.ExprT[source.VarNameKind], ...], expected_args: Tuple[source.ExprVarT[source.ProgVarName], ...]) -> Tuple[Dict[source.ExprVarT[source.HumanVarName], source.ExprT[source.VarNameKind]], source.ExprT[source.VarNameKind]]:
    conversion_map: Dict[source.ExprVarT[source.HumanVarName],
                         source.ExprT[source.VarNameKind]] = {}

    assert len(expected_args) == len(args)

    for garg, earg in zip(args, expected_args):
        assert garg.typ == earg.typ
        conversion_map[source.ExprVar(earg.typ, source.HumanVarName(
            source.HumanVarNameSubject(earg.name.split('___')[0]), path=(), use_guard=False))] = garg

    def f(v: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.VarNameKind]:
        if isinstance(v.name.subject, str) and is_global_smt(v.name.subject):
            e = source.ExprVar(source.TypeBitVec(
                PLATFORM_CONTEXT_BIT_SIZE), source.ProgVarName(v.name.subject))
            return e  # type: ignore
        if v not in conversion_map:
            for key, value in conversion_map.items():
                print(key)
        return conversion_map[v]
    return (conversion_map, source.convert_expr_vars(f, raw_precondition))


def is_special_return_variable(name: source.ProgVarName) -> bool:
    return name.startswith("ret__") and not name.startswith("ret___")


def unify_postconds(raw_postcondition: source.ExprT[source.HumanVarName],
                    rets: Tuple[source.ExprT[source.VarNameKind], ...], expected_rets: Tuple[source.ExprVarT[source.ProgVarName], ...],
                    conversion_map: Dict[source.ExprVarT[source.HumanVarName], source.ExprT[source.VarNameKind]]) -> source.ExprT[source.VarNameKind]:
    assert len(rets) == len(expected_rets)

    # this relies on the assumption that there is only one c return variable
    num_rets = 0
    for gret, eret in zip(rets, expected_rets):
        if is_special_return_variable(eret.name):
            name = source.HumanVarName(
                source.HumanVarNameSpecial.RET, path=(), use_guard=False)
            num_rets += 1
        else:
            name = source.HumanVarName(source.HumanVarNameSubject(
                eret.name), path=(), use_guard=False)
        conversion_map[source.ExprVar(eret.typ, name)] = gret

    assert num_rets <= 1, "multiple return variables were found"

    def f(v: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.VarNameKind]:
        # HACK for deliverable
        if isinstance(v.name.subject, str) and is_global_smt(v.name.subject):
            e = source.ExprVar(source.TypeBitVec(
                PLATFORM_CONTEXT_BIT_SIZE), source.ProgVarName(v.name.subject))
            return e  # type: ignore
        return conversion_map[v]

    return source.convert_expr_vars(f, raw_postcondition)


def sprinkle_handlerloop(fn: Function) -> Function:
    handler_loop_node = ghost_data.handler_loop_node_name()
    pre_after_name = source.NodeName(handler_loop_node)
    post_before_name = source.NodeName(handler_loop_node)

    def get_pre_insertion(node_name: source.NodeName, before: source.NodeName) -> Insertion:
        pre_expr = ghost_data.handler_loop_iter_pre()
        return Insertion(after=pre_after_name, before=before, kind=K.NODE_LOOP_INVARIANT_ASSUMPTION, expr=pre_expr, node_name=node_name)

    def get_post_insertion(node_name: source.NodeName, after: source.NodeName) -> Insertion:
        post_expr = ghost_data.handler_loop_iter_post()
        return Insertion(after=after, before=post_before_name, kind=K.NODE_LOOP_INVARIANT_PROOF_OBLIGATION, expr=post_expr, node_name=node_name)

    insertions = []
    for node_name in fn.traverse_topologically():
        if node_name.startswith(f'loop_{handler_loop_node}_inv_asm_'):
            before_name = node_name
            split = node_name.split(f'loop_{handler_loop_node}_inv_asm_')
            # one integer, one number
            assert len(split) == 2
            # python raises ValueError for invalid parse attempts
            num = int(split[1])
            new_node_name = source.NodeName(f'handler_loop_pre_assume_{num}')
            insertions.append(get_pre_insertion(new_node_name, before_name))

        if node_name.startswith(f'loop_{handler_loop_node}_latch_'):
            after_name = node_name
            split = node_name.split(f'loop_{handler_loop_node}_latch_')
            assert len(split) == 2
            num = int(split[1])
            if (node_name, post_before_name) not in fn.cfg.back_edges:
                continue
            new_node_name = source.NodeName(f'handler_loop_post_assert_{num}')
            insertions.append(get_post_insertion(new_node_name, after_name))

    new_nodes = apply_insertions(fn, insertions)
    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, fn.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == fn.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    return Function(name=fn.name, nodes=new_nodes, cfg=cfg, loops=loops, ghost=fn.ghost, signature=fn.signature)


def sprinkle_call_conditions(filename: str, fn: nip.Function, ctx: Dict[str, source.FunctionSignature[source.ProgVarName]]) -> Tuple[Iterator[Insertion], Iterator[Insertion]]:
    insertions: Iterator[Insertion] = iter([])
    second_run_insertions: Iterator[Insertion] = iter([])
    for name in fn.traverse_topologically(skip_err_and_ret=True):
        node = fn.nodes[name]
        if not isinstance(node,  source.NodeCall):
            continue

        ghost = ghost_data.get(filename, node.fname)

        if ghost is None:
            continue

        # asserting True and assuming True is basically doing nothing
        raw_precondition = source.expr_true if ghost is None else ghost.precondition
        raw_postcondition = source.expr_true if ghost is None else ghost.postcondition
        call_target = ctx[node.fname]
        assert call_target is not None
        conversion_map, precondition = unify_preconds(
            raw_precondition, node.args, call_target.arguments)
        postcondition = unify_postconds(
            raw_postcondition, node.rets, call_target.returns, conversion_map)
        first_run, second_run = sprinkle_call_assert_preconditions(
            fn, name, precondition, ghost.precondition_assumption)
        insertions = chain(insertions, first_run)
        second_run_insertions = chain(second_run_insertions, second_run)
        assume_postcond = iter(
            [sprinkle_call_assume_postcondition(name, node, postcondition)])
        insertions = chain(insertions, assume_postcond)
    return (insertions, second_run_insertions)

# sprinkle isn't the most trustworthy sounding word, but it's the most
# descriptive one I could think of


def sprinkle_ghost_code_prime(filename: str, func: nip.Function, ctx: Dict[str, syntax.Function]) -> Function:
    new_ctx: dict[str, source.FunctionSignature[source.ProgVarName]] = {}
    for fname, syn_func in ctx.items():
        new_ctx[fname] = source.convert_function_metadata(syn_func)
    insertions: list[Insertion] = []
    insertions.extend(sprinkle_precondition(func))
    insertions.extend(sprinkle_postcondition(func))
    loop_insertions = sprinkle_loop_invariants(func)
    insertions.extend(loop_insertions)
    first_run, second_run = sprinkle_call_conditions(filename, func, new_ctx)
    insertions.extend(first_run)
    new_nodes = apply_insertions(func, insertions)
    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    # new_nodes = search_common_succs(func, cfg)

    first_run_fn = Function(name=func.name, nodes=new_nodes, cfg=cfg,
                            loops=loops, ghost=func.ghost, signature=func.signature)

    new_nodes = apply_insertions(first_run_fn, list(second_run))
    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"
    return Function(name=func.name, nodes=new_nodes, cfg=cfg, loops=loops, ghost=func.ghost, signature=func.signature)


def sprinkle_ghost_code(filename: str, func: nip.Function, ctx: Dict[str, syntax.Function]) -> Function:
    fn = sprinkle_ghost_code_prime(filename, func, ctx)
    if filename != "tests/libsel4cp_trunc.txt" and func.name != "libsel4cp.handler_loop":
        return fn
    return sprinkle_handlerloop(fn)
