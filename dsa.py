from collections import abc
from dataclasses import dataclass
import dataclasses
from typing import Collection, Mapping, NamedTuple, NewType, Set, TypeAlias
from typing_extensions import assert_never
import abc_cfg
from source import ExprSymbol, ExprType, ExprVar, Loop, LoopHeaderName, NodeBasic, NodeCall, NodeCond, NodeEmpty, NodeName, NodeNameErr, NodeNameRet, Operator, ProgVar, ProgVarName, Function, Node, Update, all_vars_in_expr, assigned_variables_in_node, expr_where_vars_are_used_in_node, pretty_expr_ascii, used_variables_in_node, ExprOp, Expr, ExprNum
from utils import clen, set_intersection, set_union


IncarnationNum = NewType('IncarnationNum', int)
IncarnationBase = IncarnationNum(1)


class DSAVarName(NamedTuple):
    prog: ProgVarName
    inc: IncarnationNum


DSAVar: TypeAlias = ExprVar[DSAVarName]


def make_dsa_var_name(v: ProgVarName, k: IncarnationNum) -> DSAVarName:
    return DSAVarName(v, k)


def unpack_dsa_var_name(v: DSAVarName) -> tuple[ProgVarName, IncarnationNum]:
    return v.prog, v.inc


def unpack_dsa_var(var: DSAVar) -> tuple[ProgVar, IncarnationNum]:
    return ExprVar(var.typ, var.name.prog), var.name.inc


def make_dsa_var(v: ProgVar, inc: IncarnationNum) -> DSAVar:
    return ExprVar(v.typ, make_dsa_var_name(v.name, inc))


@dataclass
class DSABuilder:
    original_func: Function[ProgVarName]

    dsa_nodes: dict[NodeName, Node[DSAVarName]]
    """
    Mutated during construction
    """

    incarnations: dict[NodeName, Mapping[ProgVar, set[IncarnationNum]]]
    """
    node_name => prog_var_name => set of incarnation numbers

    mutated during construction
    """

    insertions: dict[NodeName, Mapping[ProgVar, IncarnationNum]]
    """ Nodes to insert (join nodes)

    node_name => prog_var_name => incarnation number

    (there can only be one inserted incarnated number per node per var because
    otherwise we would merge the two together).

    Mutable during construction
    """


def compute_node_variable_dependencies(func: Function[ProgVarName]) -> Mapping[NodeName, Set[ProgVar]]:
    """
    For a given node name n, deps[n] gives the set of variables that are
    refered to in n or any of its (possibly indirect) successors.
    """
    deps: dict[NodeName, Set[ProgVar]] = {}
    for node_name in func.traverse_topologically_bottom_up():
        if node_name in (NodeNameErr, NodeNameRet):
            deps[node_name] = set()
            continue
        deps[node_name] = used_variables_in_node(func.nodes[node_name]).union(
            *(deps[succ] for succ in func.cfg.all_succs[node_name] if (node_name, succ) not in func.cfg.back_edges))

    return deps


def apply_incarnations(
        context: Mapping[ProgVar, Set[IncarnationNum]],
        root: Expr[ProgVarName]) -> Expr[DSAVarName]:
    """ applies incarnation, but if a variable isn't defined in the context, it silently uses base as the incarnation count.
    """

    if isinstance(root, ExprNum):
        return root
    elif isinstance(root, ExprVar):
        var: ProgVar = ExprVar(root.typ, root.name)

        if var not in context:
            # the variable wasn't defined in *any* predecessor
            # however, this might be fine, for example:
            #
            # int a; if (0) return a + 1;
            incarnation_number = IncarnationBase
        else:
            incarnation_number = max(context[var])

        dsa_name = make_dsa_var_name(root.name, incarnation_number)

        return ExprVar(root.typ, name=dsa_name)
    elif isinstance(root, ExprOp):
        return ExprOp(root.typ, Operator(root.operator), operands=tuple(
            apply_incarnations(context, operand) for operand in root.operands
        ))
    elif isinstance(root, ExprType | ExprSymbol):
        return root
    assert_never(root)


def get_next_dsa_var_incarnation_number(s: DSABuilder, current_node: NodeName, var: ProgVar) -> IncarnationNum:
    max_inc_num: IncarnationNum | None = None
    if current_node in s.insertions and var in s.insertions[current_node]:
        max_inc_num = s.insertions[current_node][var]

    for pred_name in s.original_func.acyclic_preds_of(current_node):
        if var not in s.incarnations[pred_name]:
            continue
        for inc in s.incarnations[pred_name][var]:
            if max_inc_num is None or inc > max_inc_num:
                max_inc_num = inc

    if not max_inc_num:
        return IncarnationBase

    return IncarnationNum(max_inc_num + IncarnationNum(1))


def get_next_dsa_var_incarnation_number_from_context(s: DSABuilder, context: Mapping[ProgVar, set[IncarnationNum]], var: ProgVar) -> IncarnationNum:
    if var in context:
        return IncarnationNum(max(context[var]) + IncarnationNum(1))
    return IncarnationBase


def apply_insertions(s: DSABuilder):
    prog_var_deps = compute_node_variable_dependencies(s.original_func)

    j = 0
    for node_name, node_insertions in s.insertions.items():
        for pred_name in s.original_func.acyclic_preds_of(node_name):

            updates: list[Update[DSAVarName]] = []
            for prog_var, new_incarnation_number in node_insertions.items():
                # some variables might not be defined on all paths and still
                # represent legal code
                # good examples: dsa.txt@fail_arr_undefined_behaviour
                #                dsa.txt@shift_diag  (look at the ret variable)
                if prog_var not in s.incarnations[pred_name]:
                    continue

                # the successors don't need this variable, so don't emit a
                # joiner
                if prog_var not in prog_var_deps[node_name]:
                    continue

                old_incarnation_number = max(
                    s.incarnations[pred_name][prog_var])

                updates.append(Update(make_dsa_var(prog_var, new_incarnation_number),
                                      ExprVar(prog_var.typ, name=make_dsa_var_name(prog_var.name, old_incarnation_number))))
            if len(updates) == 0:
                continue

            j += 1
            join_node_name = NodeName(f'j{j}')
            pred = s.dsa_nodes[pred_name]
            if isinstance(pred, NodeCond):
                assert node_name in (pred.succ_then, pred.succ_else)
                if node_name == pred.succ_then:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_then=join_node_name)
                else:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_else=join_node_name)
            elif isinstance(pred, NodeBasic | NodeEmpty | NodeCall):
                # carefull, type hints for dataclasses.replace are too
                # permissive right now
                s.dsa_nodes[pred_name] = dataclasses.replace(
                    pred, succ=join_node_name)
            else:
                assert_never(pred)

            assert len(updates) > 0, f"{node_insertions=}"
            join_node = NodeBasic(tuple(updates), node_name)
            s.dsa_nodes[join_node_name] = join_node


def recompute_loops_post_dsa(s: DSABuilder, dsa_loop_targets: Mapping[LoopHeaderName, tuple[DSAVar, ...]], new_cfg: abc_cfg.CFG) -> Mapping[LoopHeaderName, Loop[DSAVarName]]:
    """ Update the loop nodes (because dsa inserts some joiner nodes)
    but keep everything else the same (in particular the loop targets are still ProgVarName!)
    """
    abc_cfg.assert_single_loop_header_per_loop(new_cfg)

    # loop header => loop nodes
    all_loop_nodes: dict[LoopHeaderName, tuple[NodeName, ...]] = {}
    for back_edge in new_cfg.back_edges:
        _, loop_header = back_edge
        loop_nodes = abc_cfg.compute_natural_loop(new_cfg, back_edge)

        assert all(loop_header in new_cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        all_loop_nodes[LoopHeaderName(loop_header)] = loop_nodes

    assert all_loop_nodes.keys() == s.original_func.loops.keys(
    ), "loop headers should remain the same through DSA transformation"

    loops: dict[LoopHeaderName, Loop[DSAVarName]] = {}
    for loop_header, loop_nodes in all_loop_nodes.items():
        assert set(s.original_func.loops[loop_header].nodes).issubset(
            loop_nodes), "dsa only inserts joiner nodes, all previous loop nodes should still be loop nodes"
        loops[loop_header] = Loop(back_edge=s.original_func.loops[loop_header].back_edge,
                                  targets=dsa_loop_targets[loop_header],
                                  nodes=loop_nodes)
    return loops


def pretty_path_condition(func: Function[ProgVarName], path: Collection[NodeName]) -> str:
    conds: list[str] = []
    for n in path:
        node = func.nodes[n]
        if isinstance(node, NodeCond) and node.succ_else != NodeNameErr:
            # TODO: do better than str
            conds.append(pretty_expr_ascii(node.expr))
    return ' and '.join(conds)


Path: TypeAlias = tuple[NodeName, ...]


def display_warning_used_but_sometimes_assigned_to_vars(func: Function[ProgVarName]):
    all_vars = set_union(used_variables_in_node(func.nodes[n]) | assigned_variables_in_node(
        func, n) for n in func.traverse_topologically() if n not in (NodeNameErr, NodeNameRet))

    # we say a variable is _assigned_ it ever was on the lhs of an assignment

    # we say a variable is _defined_ if it was assigned to an expression which
    # only depends defined variables (we start with a set a defined variable,
    # for example function arguments)

    # TODO: figure out if it suffices to prove that no unassigned variable is
    # ever used to show that no undefined variable is ever used.

    # node name => variable => paths along which the variable isn't defined
    # (so if vars_undefined_on_paths[n][v] is empty, that means v is defined
    # at node n). All paths to node n end with n.
    vars_undefined_on_paths: dict[NodeName, Mapping[ProgVar, Set[Path]]] = {}

    for n in func.traverse_topologically():
        if n in (NodeNameRet, NodeNameErr):
            continue

        node = func.nodes[n]
        preds = func.acyclic_preds_of(n)
        if clen(preds) == 0:
            # TODO: include globals
            vars_undefined_on_paths[n] = {var: set() if var in func.arguments else {
                (n, )} for var in all_vars}
        else:
            # 1. merge preds:

            # 1.a. merge all preds (for each variable, union of path)
            local: dict[ProgVar, Set[Path]] = {var: set_union(
                vars_undefined_on_paths[p][var] for p in func.acyclic_preds_of(n)) for var in all_vars}

            # 1.b. if a variable is assigned in the current node, set paths to
            # the union of the paths of the variables the rhs depends on
            if isinstance(node, NodeBasic):
                base = dict(local)  # copy
                # notice that we don't read from local! That's because updates
                # are simultaneous, node.upds[0] shouldn't impact node.upds[1]
                for upd in node.upds:
                    assert all_vars_in_expr(upd.expr) < all_vars
                    assert upd.var in all_vars, "this means (1) we missed a variable (2) we are assigning to an unused variable"
                    local[upd.var] = set_union(base[var]
                                               for var in all_vars_in_expr(upd.expr))
            elif isinstance(node, NodeCall):
                # ret0, ret1, ..., retN = f(arg0(v00,v01,...), arg1(v10,v11,...), ..., argM(vM0,vM1,...))
                # all argI are expressions that depend on multiple variables
                # all retI depend on all vJK

                # all the variables we depend on to evaluate f(...)
                var_deps: set[ProgVar] = set_union(
                    all_vars_in_expr(arg) for arg in node.args)

                # all the paths we must avoid to evaluate f(...)
                path_deps: set[Path] = set_union(
                    local[var] for var in var_deps)

                for ret in node.rets:
                    local[ret] = path_deps
            elif not isinstance(node, NodeEmpty | NodeCond):
                assert_never(node)

            # 2. add current node to all the paths
            for var, paths in local.items():
                local[var] = set(path + (n, ) for path in paths)

            vars_undefined_on_paths[n] = local

    for n in func.traverse_topologically():
        if n in (NodeNameErr, NodeNameRet):
            continue

        node = func.nodes[n]
        vars_undefined = set(
            v for v, paths in vars_undefined_on_paths[n].items() if len(paths) > 0)
        used_but_undefined = used_variables_in_node(node) & set(vars_undefined)

        if len(used_but_undefined) > 0:
            # this is an over approximation. For example, we could have an
            # expression like `if x then a else b` where b is undefined. It would
            # suffice to prove that path_condition & !x cannot be true. Right
            # now, we don't look at the expression, we just ensure that
            # path_condition cannot be true.

            # we have unused but undefined variables
            break
    else:
        return  # we don't have any problems :)

    print("DYNAMIC SINGLE ASSIGNMENT WARNING")
    print("=================================")
    print()
    print(f"In function {func.name}")
    print(f"Some variables used in some expression aren't always initialized")
    print(f"It might reveal that these paths are impossible to take")
    print(f"It might reveal the expressions won't ever evaluate those variables")
    print(f"This should be determined by the SMT solvers.")
    print()
    print(f"NOTE: the s suffix on operators means signed (>>s means _signed_ shift right)")
    for n in func.traverse_topologically():
        if n in (NodeNameErr, NodeNameRet):
            continue

        node = func.nodes[n]
        vars_undefined = set(
            v for v, paths in vars_undefined_on_paths[n].items() if len(paths) > 0)
        for var, expr in sorted(expr_where_vars_are_used_in_node(node, vars_undefined)):
            print()
            print(
                f"Variable `{var.name}` is used in expr `{pretty_expr_ascii(expr)}`")
            print(f"But if one of the following condition is true, it isn't defined")
            for path in vars_undefined_on_paths[n][var]:
                print(
                    f"  - {pretty_path_condition(func, path) or 'true'} (path: {' '.join(path)})")


def dsa(func: Function[ProgVarName]) -> Function[DSAVarName]:

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

    entry_incarnations: dict[ProgVar, set[IncarnationNum]] = {}
    dsa_args: list[DSAVar] = []
    for arg in func.arguments:
        dsa_args.append(make_dsa_var(arg, IncarnationBase))
        entry_incarnations[arg] = {IncarnationBase}

    assert len(set(unpack_dsa_var_name(arg.name)[0] for arg in dsa_args)) == len(
        dsa_args), "unexpected duplicate argument name"

    dsa_loop_targets: dict[LoopHeaderName, tuple[DSAVar, ...]] = {}
    for current_node in func.traverse_topologically():

        if current_node in (NodeNameErr, NodeNameRet):
            continue

        # build up a context (map from prog var to incarnation numbers)
        # TODO: clean this up
        context: dict[ProgVar, set[IncarnationNum]]
        curr_node_insertions: dict[ProgVar, IncarnationNum] | None = None
        if current_node == func.cfg.entry:
            context = entry_incarnations
        else:
            context = {}
            curr_node_insertions = {}

            all_variables: set[ProgVar] = set_union(set(s.incarnations[p].keys(
            )) for p in s.original_func.acyclic_preds_of(current_node))

            for var in all_variables:
                context[var] = set_intersection(s.incarnations[p][var] for p in s.original_func.acyclic_preds_of(
                    current_node) if var in s.incarnations[p])

                if len(context[var]) == 0:
                    # predecessors have no incarnation numbers in common, we need to insert a join node
                    # optimisation: get rid of the + 1 and do smarter joins
                    fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                        s, current_node, var)
                    curr_node_insertions[var] = fresh_incarnation_number
                    context[var] = {fresh_incarnation_number}

            if curr_node_insertions:
                # we need to insert some join nodes
                s.insertions[current_node] = curr_node_insertions

        if loop_header := func.is_loop_header(current_node):
            targets: list[DSAVar] = []

            for target in func.loops[loop_header].targets:
                # havoc the loop targets
                fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                    s, current_node, target)
                context[target] = {fresh_incarnation_number}
                targets.append(make_dsa_var(
                    target, fresh_incarnation_number))

            dsa_loop_targets[loop_header] = tuple(targets)

        added_incarnations: dict[ProgVar, DSAVar] = {}

        # print(f'{current_node=}')
        # print(f'{curr_node_insertions=}')
        # for var in context:
        #     print(
        #         f'  {var.name}', context[var], '  [joiner]' if curr_node_insertions and var in curr_node_insertions else '')

        node = func.nodes[current_node]
        if isinstance(node, NodeBasic):
            upds: list[Update[DSAVarName]] = []
            for upd in node.upds:
                # notice that we don't take into consideration the previous
                # updates from the same node. That's because the updates are
                # simultaneous.
                expr = apply_incarnations(context, upd.expr)
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, upd.var)
                dsa_var = make_dsa_var(upd.var, inc)
                upds.append(Update(dsa_var, expr))
                assert upd.var not in added_incarnations, "duplicate updates in BasicNode"
                added_incarnations[upd.var] = dsa_var

            s.dsa_nodes[current_node] = NodeBasic(tuple(upds), succ=node.succ)
        elif isinstance(node, NodeCond):
            s.dsa_nodes[current_node] = NodeCond(
                expr=apply_incarnations(context, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, NodeCall):
            args = tuple(apply_incarnations(context, arg)
                         for arg in node.args)

            rets: list[DSAVar] = []
            for ret in node.rets:
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, ret)
                rets.append(make_dsa_var(ret, inc))
                added_incarnations[ret] = rets[-1]

            s.dsa_nodes[current_node] = NodeCall(
                succ=node.succ,
                args=args,
                rets=tuple(rets),
                fname=node.fname,
            )
        elif isinstance(node, NodeEmpty):
            s.dsa_nodes[current_node] = node
        else:
            assert_never(node)

        # print("  + ")
        # for var, incs in added_incarnations.items():
        #     print(f'  {var.name}', incs.name[1])

        curr_node_incarnations = dict(context)
        for prog_var, dsa_var in added_incarnations.items():
            _, incarnation_number = unpack_dsa_var_name(dsa_var.name)
            curr_node_incarnations[prog_var] = {incarnation_number}
        s.incarnations[current_node] = curr_node_incarnations

    apply_insertions(s)

    display_warning_used_but_sometimes_assigned_to_vars(s.original_func)

    # need to recompute the cfg from dsa_nodes
    all_succs = abc_cfg.compute_all_successors_from_nodes(s.dsa_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)

    # FIXME: this function is useless
    loops = recompute_loops_post_dsa(s, dsa_loop_targets, cfg)

    return Function[DSAVarName](
        cfg=cfg,
        arguments=tuple(dsa_args),
        loops=loops,
        name=func.name,
        nodes=s.dsa_nodes)
