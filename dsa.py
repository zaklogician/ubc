import dataclasses
from typing import Generic, Mapping, NewType, Set, TypeAlias, TypeVar
from typing_extensions import assert_never
import abc_cfg
import source
import nip
import ghost_code
from utils import set_union
from dataclasses import dataclass


IncarnationNum = NewType('IncarnationNum', int)
IncarnationBase = IncarnationNum(1)

# Incarnation is immutable, so its generic parameter is covariant
# it must either be ProgVarName, GuardVarName, or ProgVarName | GuardVarName
BaseVarName = TypeVar('BaseVarName', source.ProgVarName, nip.GuardVarName,
                      source.ProgVarName | nip.GuardVarName, covariant=True)


@dataclass(frozen=True, order=True)
class Incarnation(Generic[BaseVarName]):
    base: BaseVarName
    inc: IncarnationNum


BaseVar: TypeAlias = source.ExprVarT[BaseVarName]
Var: TypeAlias = source.ExprVarT[Incarnation[BaseVarName]]


@dataclass(frozen=True)
class GenericFunction(ghost_code.GenericFunction[source.VarNameKind, source.VarNameKind2]):
    """ DSA Function """

    contexts: Mapping[source.NodeName,
                      Mapping[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum]]
    """ Mapping for each node from prog variable to the incarnation number at
        the _end_ of that node
    """


Function = GenericFunction[Incarnation[source.ProgVarName |
                                       nip.GuardVarName], source.ProgVarName | nip.GuardVarName]


@dataclass(frozen=True)
class NodeJoiner(source.NodeBasic[Incarnation[source.ProgVarName | nip.GuardVarName]]):
    pass


def unpack_dsa_var_name(v: Incarnation[BaseVarName]) -> tuple[BaseVarName, IncarnationNum]:
    return v.base, v.inc


def unpack_dsa_var(var: Var[BaseVarName]) -> tuple[source.ExprVarT[BaseVarName], IncarnationNum]:
    return source.ExprVar(var.typ, var.name.base), var.name.inc


def get_base_var(var: Var[BaseVarName]) -> BaseVar[BaseVarName]:
    return source.ExprVar(var.typ, var.name.base)


def make_dsa_var(v: source.ExprVarT[BaseVarName], inc: IncarnationNum) -> source.ExprVarT[Incarnation[BaseVarName]]:
    return source.ExprVar(v.typ, Incarnation(v.name, inc))


def guard_var_at_node(func: Function, n: source.NodeName, var: Var[source.ProgVarName]) -> Var[nip.GuardVarName]:
    guard_base_name = nip.guard_name(var.name.base)
    guard_base_var = source.ExprVar(source.type_bool, guard_base_name)
    incarnation: Incarnation[nip.GuardVarName] = Incarnation(
        guard_base_name, func.contexts[n][guard_base_var])
    return source.ExprVar(var.typ, incarnation)


@dataclasses.dataclass
class DSABuilder:
    original_func: ghost_code.Function

    dsa_nodes: dict[source.NodeName,
                    source.Node[Incarnation[nip.GuardVarName | source.ProgVarName]]]
    """
    Mutated during construction
    """

    incarnations: dict[source.NodeName,
                       Mapping[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum]]
    """
    node_name => prog_var_name => set of incarnation numbers

    mutated during construction
    """

    insertions: dict[source.NodeName,
                     Mapping[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum]]
    """ Nodes to insert (join nodes)

    node_name => prog_var_name => incarnation number

    (there can only be one inserted incarnated number per node per var because
    otherwise we would merge the two together).

    Mutable during construction
    """


def apply_incarnations(
        context: Mapping[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum],
        root: source.ExprT[BaseVarName]) -> source.ExprT[Incarnation[BaseVarName]]:
    """ applies incarnation, but if a variable isn't defined in the context, it silently uses base as the incarnation count.
    """

    if isinstance(root, source.ExprNum | source.ExprType | source.ExprSymbol):
        return root
    elif isinstance(root, source.ExprVar):
        var: source.ExprVarT[source.ProgVarName | nip.GuardVarName] = source.ExprVar(
            root.typ, root.name)

        if var not in context:
            # the variable wasn't defined in *any* predecessor
            # however, this might be fine, for example:
            #
            # int a; if (0) return a + 1;
            incarnation_number = IncarnationBase
        else:
            incarnation_number = context[var]

        dsa_name = Incarnation(root.name, incarnation_number)
        return source.ExprVar(root.typ, name=dsa_name)
    elif isinstance(root, source.ExprOp):
        return source.ExprOp(root.typ, source.Operator(root.operator), operands=tuple(
            apply_incarnations(context, operand) for operand in root.operands
        ))
    elif isinstance(root, source.ExprFunction):
        assert False, "there shouldn't be any function in the graph lang"
    assert_never(root)


def get_next_dsa_var_incarnation_number(s: DSABuilder, current_node: source.NodeName, var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> IncarnationNum:
    max_inc_num: IncarnationNum | None = None
    if current_node in s.insertions and var in s.insertions[current_node]:
        max_inc_num = s.insertions[current_node][var]

    for pred_name in s.original_func.acyclic_preds_of(current_node):
        if var not in s.incarnations[pred_name]:
            continue
        if max_inc_num is None or s.incarnations[pred_name][var] > max_inc_num:
            max_inc_num = s.incarnations[pred_name][var]

    if not max_inc_num:
        return IncarnationBase

    return IncarnationNum(max_inc_num + IncarnationNum(1))


def get_next_dsa_var_incarnation_number_from_context(s: DSABuilder, context: Mapping[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum], var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> IncarnationNum:
    if var in context:
        return IncarnationNum(context[var] + IncarnationNum(1))
    return IncarnationBase


def apply_insertions(s: DSABuilder) -> None:
    j = 0
    for node_name, node_insertions in s.insertions.items():
        for pred_name in s.original_func.acyclic_preds_of(node_name):

            updates: list[source.Update[Incarnation[source.ProgVarName | nip.GuardVarName]]] = [
            ]
            for prog_var, new_incarnation_number in node_insertions.items():
                # some variables might not be defined on all paths and still
                # represent legal code
                # good examples: dsa.txt@fail_arr_undefined_behaviour
                #                dsa.txt@shift_diag  (look at the ret variable)
                if prog_var not in s.incarnations[pred_name]:
                    continue

                old_incarnation_number = s.incarnations[pred_name][prog_var]

                updates.append(source.Update(make_dsa_var(prog_var, new_incarnation_number),
                                             source.ExprVar(prog_var.typ, name=Incarnation(prog_var.name, old_incarnation_number))))
            if len(updates) == 0:
                continue

            j += 1
            join_node_name = source.NodeName(f'j{j}')
            pred = s.dsa_nodes[pred_name]
            if isinstance(pred, source.NodeCond):
                assert node_name in (pred.succ_then, pred.succ_else)
                if node_name == pred.succ_then:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_then=join_node_name)
                else:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_else=join_node_name)
            elif isinstance(pred, source.NodeBasic | source.NodeEmpty | source.NodeCall | source.NodeAssume):
                # careful, type hints for dataclasses.replace are too
                # permissive right now
                s.dsa_nodes[pred_name] = dataclasses.replace(
                    pred, succ=join_node_name)
            else:
                assert_never(pred)

            assert len(updates) > 0, f"{node_insertions=}"
            join_node = NodeJoiner(tuple(updates), node_name)
            s.dsa_nodes[join_node_name] = join_node
            assert join_node_name not in s.incarnations

            incarnation_at_joiner_node: dict[source.ExprVarT[source.ProgVarName | nip.GuardVarName], IncarnationNum] = dict(
                s.incarnations[pred_name])
            for upd in updates:
                incarnation_at_joiner_node[get_base_var(
                    upd.var)] = upd.var.name.inc
            s.incarnations[join_node_name] = incarnation_at_joiner_node


def recompute_loops_post_dsa(s: DSABuilder, dsa_loop_targets: Mapping[source.LoopHeaderName, tuple[Var[BaseVarName], ...]], new_cfg: abc_cfg.CFG) -> Mapping[source.LoopHeaderName, source.Loop[Incarnation[BaseVarName]]]:
    abc_cfg.assert_single_loop_header_per_loop(new_cfg)

    # loop header => loop nodes
    all_loop_nodes: dict[source.LoopHeaderName,
                         tuple[source.NodeName, ...]] = {}
    for back_edge in new_cfg.back_edges:
        _, loop_header = back_edge
        loop_nodes = abc_cfg.compute_natural_loop(new_cfg, back_edge)

        assert all(loop_header in new_cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        all_loop_nodes[source.LoopHeaderName(loop_header)] = loop_nodes

    assert all_loop_nodes.keys() == s.original_func.loops.keys(
    ), "loop headers should remain the same through DSA transformation"

    loops: dict[source.LoopHeaderName,
                source.Loop[Incarnation[BaseVarName]]] = {}
    for loop_header, loop_nodes in all_loop_nodes.items():
        assert set(s.original_func.loops[loop_header].nodes).issubset(
            loop_nodes), "dsa only inserts joiner nodes, all previous loop nodes should still be loop nodes"
        loops[loop_header] = source.Loop(back_edge=s.original_func.loops[loop_header].back_edge,
                                         targets=dsa_loop_targets[loop_header],
                                         nodes=loop_nodes)
    return loops


def dsa(func: ghost_code.Function) -> Function:
    """
    Returns the dsa function, and an artifact to make it easy to emit
    expressions into the DSA later on (used to emit the loop invariants)
    """

    # for each node, for each prog variable, keep a set of possible dsa incarnations
    # (this is going to use a lot of memory but oh well)
    #
    # when getting the latest incarnation, lookup it in the insertions for the
    # current node. If there, return the incarnation. Otherwise, look in the
    # predecessors. If they all return the same incarnation, return that.
    # Otherwise,
    #   - fresh_var = (prog_var_name, max(inc num) + 1)
    #   - record an insertion (current node, prog_var_name, fresh_var)
    #   - return fresh_var
    #
    # at the end, apply the insertions
    # recompute cfg

    s = DSABuilder(original_func=func, insertions={},
                   dsa_nodes={}, incarnations={})

    entry_context: dict[source.ExprVarT[source.ProgVarName |
                                        nip.GuardVarName], IncarnationNum] = {}
    dsa_args: list[source.ExprVarT[Incarnation[source.ProgVarName |
                                               nip.GuardVarName]]] = []
    for arg in func.arguments:
        dsa_args.append(make_dsa_var(arg, IncarnationBase))
        entry_context[arg] = IncarnationBase

    assert len(set(unpack_dsa_var_name(arg.name)[0] for arg in dsa_args)) == len(
        dsa_args), "unexpected duplicate argument name"

    dsa_loop_targets: dict[source.LoopHeaderName,
                           tuple[Var[source.ProgVarName | nip.GuardVarName], ...]] = {}
    for current_node in func.traverse_topologically():

        if current_node in (source.NodeNameErr, source.NodeNameRet):
            continue

        node = func.nodes[current_node]

        # build up a context (map from prog var to incarnation numbers)
        # TODO: clean this up
        context: dict[source.ExprVarT[source.ProgVarName |
                                      nip.GuardVarName], IncarnationNum]
        curr_node_insertions: dict[source.ExprVarT[source.ProgVarName | nip.GuardVarName],
                                   IncarnationNum] | None = None
        if current_node == func.cfg.entry:
            context = dict(entry_context)
        else:
            context = {}
            curr_node_insertions = {}

            all_variables: set[source.ExprVarT[source.ProgVarName | nip.GuardVarName]] = set_union(set(s.incarnations[p].keys(
            )) for p in s.original_func.acyclic_preds_of(current_node))

            for var in all_variables:
                possibilities = set(s.incarnations[p][var] for p in s.original_func.acyclic_preds_of(
                    current_node) if var in s.incarnations[p])

                if len(possibilities) > 1:
                    # predecessors disagree about predecessors, we need to insert a join node
                    fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                        s, current_node, var)
                    curr_node_insertions[var] = fresh_incarnation_number
                    context[var] = fresh_incarnation_number
                elif len(possibilities) == 1:
                    context[var] = next(iter(possibilities))
                else:
                    assert False, "I didn't think this case was possible"

            if curr_node_insertions:
                # we need to insert some join nodes
                s.insertions[current_node] = curr_node_insertions

        if loop_header := func.is_loop_header(current_node):
            targets: list[Var[source.ProgVarName | nip.GuardVarName]] = []

            for target in func.loops[loop_header].targets:
                # havoc the loop targets
                fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                    s, current_node, target)
                context[target] = fresh_incarnation_number
                targets.append(make_dsa_var(
                    target, fresh_incarnation_number))

            dsa_loop_targets[loop_header] = tuple(targets)

        if isinstance(node, ghost_code.NodePostConditionProofObligation):
            # we need to use the entry's context for the argument variables in
            # the post condition, eg
            #
            #     int add_one(int n)
            #     ensures ret == n + 1
            #     {
            #         n = 0;         // n2 = 0
            #         return 1;      // prove 1 == n1 + 1    ; notice n1, not n2
            #     }
            #
            # This function shouldn't verify. From the perspective of the
            # caller,
            #
            #     add_one(3) == 4, not 1
            #
            # But for local variable, it should be just regular DSA
            #
            #     int add(int a, int b)
            #     ensures ret == a + b
            #     {
            #         int sum = 0;      // sum1 = 0
            #         sum = sum + a;    // sum2 = sum1 + a1
            #         sum = sum + b;    // sum3 = sum2 + b1
            #         a = 0;            // a2 = 0
            #         b = 0;            // b2 = 0
            #         return sum;       // prove sum3 = a1 + b1   ; notice sum3, not sum1
            #     }
            #
            # using a different context in the middle of the graph could
            # result in some very weird behavior. This doesn't matter because
            # the post condition proof obligation is right at the bottom of
            # the function. So to be safe, we validate those assumptions
            assert node.succ_then == source.NodeNameRet
            assert node.succ_else == source.NodeNameErr

            # in the post condition, when you mention a function argument, you
            # mean its value at the start of the function.
            for arg in func.arguments:
                context[arg] = entry_context[arg]

        added_incarnations: dict[source.ExprVarT[source.ProgVarName |
                                                 nip.GuardVarName], Var[source.ProgVarName | nip.GuardVarName]] = {}

        # print(f'{current_node=}')
        # print(f'{curr_node_insertions=}')
        # for var in context:
        #     print(
        #         f'  {var.name}', context[var], '  [joiner]' if curr_node_insertions and var in curr_node_insertions else '')

        # it's important that we use dataclasses.replace here because node
        # might be a subtype of NodeBasic/NodeCond, and we don't want to
        # lose that information by using the constructor explicitely
        if isinstance(node, source.NodeBasic):
            upds: list[source.Update[Incarnation[source.ProgVarName |
                                                 nip.GuardVarName]]] = []
            for upd in node.upds:
                # notice that we don't take into consideration the previous
                # updates from the same node. That's because the updates are
                # simultaneous.
                expr = apply_incarnations(context, upd.expr)
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, upd.var)
                dsa_var = make_dsa_var(upd.var, inc)
                upds.append(source.Update(dsa_var, expr))
                assert upd.var not in added_incarnations, "duplicate updates in BasicNode"
                added_incarnations[upd.var] = dsa_var

            # mypy doesn't know about dataclasses.replace anyway, so it
            # doesn't provide any guarantees. That also means it's not able
            # to figure out that node will now be of the right type, so this
            # type ignore is required.
            s.dsa_nodes[current_node] = dataclasses.replace(   # type: ignore
                node, upds=tuple(upds))
        elif isinstance(node, source.NodeCond):
            s.dsa_nodes[current_node] = dataclasses.replace(     # type: ignore
                node, expr=apply_incarnations(context, node.expr))
        elif isinstance(node, source.NodeCall):
            args = tuple(apply_incarnations(context, arg)
                         for arg in node.args)

            rets: list[Var[source.ProgVarName | nip.GuardVarName]] = []
            for ret in node.rets:
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, ret)
                rets.append(make_dsa_var(ret, inc))
                added_incarnations[ret] = rets[-1]

            s.dsa_nodes[current_node] = dataclasses.replace(   # type: ignore
                node, args=args, rets=tuple(rets))
        elif isinstance(node, source.NodeAssume):
            s.dsa_nodes[current_node] = dataclasses.replace(   # type: ignore
                node, expr=apply_incarnations(context, node.expr))
        elif isinstance(node, source.NodeEmpty):
            s.dsa_nodes[current_node] = node
        else:
            assert_never(node)

        # print("  + ")
        # for var, incs in added_incarnations.items():
        #     print(f'  {var.name}', incs.name[1])

        curr_node_incarnations = dict(context)
        for prog_var, dsa_var in added_incarnations.items():
            _, incarnation_number = unpack_dsa_var_name(dsa_var.name)
            curr_node_incarnations[prog_var] = incarnation_number
        s.incarnations[current_node] = curr_node_incarnations

    apply_insertions(s)

    # need to recompute the cfg from dsa_nodes
    all_succs = abc_cfg.compute_all_successors_from_nodes(s.dsa_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)

    # FIXME: this function is useless
    loops = recompute_loops_post_dsa(s, dsa_loop_targets, cfg)
    # loops = abc_cfg.compute_loops(s.dsa_nodes, cfg)

    assert loops.keys() == func.loops.keys()

    return Function(
        cfg=cfg,
        arguments=tuple(dsa_args),
        returns=func.returns,
        loops=loops,
        name=func.name,
        nodes=s.dsa_nodes,
        contexts=s.incarnations,
        ghost=func.ghost)
