from typing import Collection, Sequence, Set
from typing_extensions import assert_never
import abc_cfg
import source
import nip
import ghost_code
import dsa


def compute_all_path(cfg: abc_cfg.CFG) -> Sequence[Sequence[source.NodeName]]:
    # binary number, 1 means go left 0 means go right
    # start exploring tree all the way from the left
    all_paths: list[list[source.NodeName]] = []

    def dfs(n: source.NodeName) -> None:
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


def ensure_assigned_at_most_once(func: dsa.Function, path: Collection[source.NodeName]) -> None:
    """ Ensure that each variable (name, typ) is assigned at most once
    """
    assigned_variables: list[dsa.Var[source.ProgVarName |
                                     nip.GuardVarName]] = []
    for n in path:
        # note that we don't use source.assigned_variables_in_node because it
        # returns a set. That is, if there are duplicates, it will hide them
        # from us.
        if n in (source.NodeNameRet, source.NodeNameErr):
            continue

        node = func.nodes[n]
        if isinstance(node, source.NodeBasic):
            assigned_variables.extend(upd.var for upd in node.upds)
        elif isinstance(node, source.NodeCall):
            assigned_variables.extend(ret for ret in node.rets)
        elif not isinstance(node, source.NodeEmpty | source.NodeCond | source.NodeAssume | source.NodeAssert):
            assert_never(node)

        if loop_header := func.is_loop_header(n):
            assigned_variables.extend(func.loops[loop_header].targets)

    assert len(assigned_variables) == len(set(assigned_variables))


def ensure_using_latest_incarnation(func: dsa.Function, path: Collection[source.NodeName]) -> None:
    latest_incarnations: dict[source.ExprVarT[source.ProgVarName |
                                              nip.GuardVarName], dsa.IncarnationNum] = {}

    # TODO: globals
    for arg in func.signature.arguments:
        prog_var, inc = dsa.unpack_dsa_var(arg)
        assert prog_var not in latest_incarnations
        latest_incarnations[prog_var] = inc

    entry_incarnations = dict(latest_incarnations)

    for n in path:
        if n in (source.NodeNameErr, source.NodeNameRet):
            continue

        for dsa_var in source.used_variables_in_node(func.nodes[n]):
            # loop targets are havoc'd at the top of the loop header
            # that is, it is legal to use them in the loop header itself
            if loop_header := func.is_loop_header(n):
                for target in func.loops[loop_header].targets:
                    prog_var, inc = dsa.unpack_dsa_var(target)
                    latest_incarnations[prog_var] = inc

            prog_var, inc = dsa.unpack_dsa_var(dsa_var)
            if isinstance(func.nodes[n], ghost_code.NodePostConditionProofObligation):
                if any(prog_var == dsa.unpack_dsa_var(dsa_var)[0] for dsa_var in func.signature.arguments):
                    assert inc == entry_incarnations[prog_var], f'{inc} {entry_incarnations[prog_var]}'
                elif prog_var in latest_incarnations:
                    # FIXME: we shouldn't need this condition here
                    #        this is only because of the assert False node
                    #        TODO: skip this test if the start node isn't reachable
                    #              from the entry node
                    assert inc == latest_incarnations[prog_var], f'{inc} {latest_incarnations[prog_var]}'
            elif prog_var in latest_incarnations:
                assert inc == latest_incarnations[prog_var], f"{prog_var=} {n=} {path=}"

            # we don't assert that inc == 1 otherwise, because prog_var:1
            # might be used on some other path that joins with our own(and so
            # inc would be 2 for example)

        for dsa_var in source.assigned_variables_in_node(func, n, with_loop_targets=True):
            prog_var, inc = dsa.unpack_dsa_var(dsa_var)
            latest_incarnations[prog_var] = inc


def ensure_valid_dsa(dsa_func: dsa.Function) -> None:
    all_paths = compute_all_path(dsa_func.cfg)
    for i, path in enumerate(all_paths):
        ensure_assigned_at_most_once(dsa_func, path)
        ensure_using_latest_incarnation(dsa_func, path)


def assert_expr_equals_mod_dsa(lhs: source.ExprT[source.ProgVarName | nip.GuardVarName], rhs: source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> None:
    assert lhs.typ == rhs.typ

    if isinstance(lhs, source.ExprNum | source.ExprSymbol | source.ExprType):
        assert lhs == rhs
    elif isinstance(lhs, source.ExprVar):
        assert isinstance(rhs, source.ExprVar)
        assert lhs.name == dsa.unpack_dsa_var_name(rhs.name)[0]
    elif isinstance(lhs, source.ExprOp):
        assert isinstance(rhs, source.ExprOp)
        assert lhs.operator == rhs.operator
        assert len(lhs.operands) == len(rhs.operands)
        for i in range(len(lhs.operands)):
            assert_expr_equals_mod_dsa(lhs.operands[i], rhs.operands[i])
    elif isinstance(lhs, source.ExprFunction):
        assert isinstance(rhs, source.ExprFunction)
        assert lhs.function_name == rhs.function_name
        assert len(lhs.arguments) == len(rhs.arguments)
        for i in range(len(lhs.arguments)):
            assert_expr_equals_mod_dsa(lhs.arguments[i], rhs.arguments[i])
    else:
        assert_never(lhs)


def assert_var_equals_mod_dsa(prog: source.ExprVarT[source.ProgVarName | nip.GuardVarName], var: dsa.Var[source.ProgVarName | nip.GuardVarName]) -> None:
    assert prog == dsa.unpack_dsa_var(var)[0]


def assert_node_equals_mod_dsa(prog: source.Node[source.ProgVarName | nip.GuardVarName], node: source.Node[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> None:
    if isinstance(prog, source.NodeBasic):
        assert isinstance(node, source.NodeBasic)

        assert len(prog.upds) == len(node.upds)
        for i in range(len(prog.upds)):
            assert_var_equals_mod_dsa(
                prog.upds[i].var, node.upds[i].var)

            assert_expr_equals_mod_dsa(
                prog.upds[i].expr, node.upds[i].expr)

    elif isinstance(prog, source.NodeCall):
        assert isinstance(node, source.NodeCall)

        assert len(prog.args) == len(node.args)
        for i in range(len(prog.args)):
            assert_expr_equals_mod_dsa(prog.args[i], node.args[i])

        assert len(prog.rets) == len(node.rets)
        for i in range(len(prog.rets)):
            assert_var_equals_mod_dsa(prog.rets[i], node.rets[i])

    elif isinstance(prog, source.NodeCond):
        assert isinstance(node, source.NodeCond)
        assert_expr_equals_mod_dsa(prog.expr, node.expr)

    elif isinstance(prog, source.NodeAssume | source.NodeAssert):
        assert isinstance(node, source.NodeAssume | source.NodeAssert)
        assert_expr_equals_mod_dsa(prog.expr, node.expr)

    elif isinstance(prog, source.NodeEmpty):
        assert isinstance(node, source.NodeEmpty)
    else:
        assert_never(prog)


def assert_is_join_node(node: source.Node[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> None:
    assert isinstance(node, dsa.NodeJoiner)
    for upd in node.upds:
        # ensure every update is of the form A.X = A.Y
        lhs_name, _ = dsa.unpack_dsa_var_name(upd.var.name)
        assert isinstance(upd.expr, source.ExprVar)
        rhs_name, _ = dsa.unpack_dsa_var_name(upd.expr.name)
        assert upd.var.typ == upd.expr.typ
        assert lhs_name == rhs_name


def ensure_correspondence(prog_func: ghost_code.Function, dsa_func: dsa.Function) -> None:
    assert set(prog_func.nodes.keys()).issubset(dsa_func.nodes.keys())

    join_node_names: list[source.NodeName] = []

    for node_name in dsa_func.nodes:
        if node_name in (source.NodeNameErr, source.NodeNameRet):
            continue

        dsa_node = dsa_func.nodes[node_name]

        if node_name not in prog_func.nodes:
            assert_is_join_node(dsa_node)
            assert node_name.startswith('j')  # not required semantically
            join_node_names.append(node_name)
        else:
            prog_node = prog_func.nodes[node_name]
            assert_node_equals_mod_dsa(prog_node, dsa_node)

    for node_name in prog_func.traverse_topologically():
        prog_succs = prog_func.cfg.all_succs[node_name]
        dsa_succs = dsa_func.cfg.all_succs[node_name]

        if prog_succs == dsa_succs:
            continue

        # the only reason the successors wouldn't been the same is if a dsa.dsa
        # successor was a join node.

        assert len(prog_succs) == len(dsa_succs)
        for i in range(len(prog_succs)):
            if prog_succs[i] == dsa_succs[i]:
                continue

            # we must have
            # prog:  a -----------> b
            # dsa.dsa :  a --> join --> b

            assert dsa_succs[i] in join_node_names
            join_node_succs = dsa_func.cfg.all_succs[dsa_succs[i]]
            assert len(join_node_succs) == 1
            assert join_node_succs[0] == prog_succs[i]


def ensure_valid_contexts(func: dsa.Function) -> None:
    new_contexts: dict[source.NodeName, dict[source.ExprVarT[source.ProgVarName |
                                                             nip.GuardVarName], dsa.IncarnationNum]] = {}
    new_contexts[func.cfg.entry] = {dsa.get_base_var(
        var): dsa.IncarnationBase for var in func.signature.arguments}
    assert new_contexts[func.cfg.entry] == func.contexts[func.cfg.entry]

    for n in func.traverse_topologically(skip_err_and_ret=True):
        if n == func.cfg.entry:
            continue
        assert n not in new_contexts, f'{n=}'

        conflicting_vars: set[source.ExprVarT[source.ProgVarName |
                                              nip.GuardVarName]] = set()
        new_contexts[n] = {}
        for p in func.acyclic_preds_of(n):
            assert p in new_contexts, f'{n=} {p=}'
            for var, inc in new_contexts[p].items():

                if var in new_contexts[n] and new_contexts[n][var] != inc:
                    conflicting_vars.add(var)

                new_contexts[n][var] = inc

        assert len(conflicting_vars) == 0

        for v in source.assigned_variables_in_node(func, n, with_loop_targets=True):
            new_contexts[n][dsa.get_base_var(v)] = v.name.inc

        if isinstance(func.nodes[n], ghost_code.NodePostConditionProofObligation):
            assert isinstance(func.nodes[n], source.NodeCond)
            # in the post condition, when referencing function arguments, you
            # use initial incarnations.
            for dsa_var in func.signature.arguments:
                prog_var, inc = dsa.unpack_dsa_var(dsa_var)
                new_contexts[n][prog_var] = inc

        if new_contexts[n] != func.contexts[n]:
            diff = set(new_contexts[n].items()) ^ set(func.contexts[n].items())
            print('reference:', [(v.name, inc)
                                 for v, inc in new_contexts[n].items()])
            print('actual:   ', [(v.name, inc)
                                 for v, inc in func.contexts[n].items()])
            print('diff:     ', [(v.name, inc) for v, inc in diff])
            assert False, f"context aren't the same for node {n=}"

    assert new_contexts == func.contexts


def ensure_valid_variables(func: dsa.Function) -> None:
    """ Ensure that each variable only ever has one type """
    var_types: dict[dsa.Incarnation[source.ProgVarName |
                                    nip.GuardVarName], source.Type] = {}

    def add_or_ensure_same_typ(var_name: dsa.Incarnation[source.ProgVarName | nip.GuardVarName], typ: source.Type) -> None:
        if var_name in var_types:
            assert var_types[var_name] == typ
        var_types[var_name] = typ

    def check_expr_visitor(expr: source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> None:
        if isinstance(expr, source.ExprVar):
            add_or_ensure_same_typ(expr.name, expr.typ)

    for n, node in func.nodes.items():
        if isinstance(node, source.NodeBasic):
            for upd in node.upds:
                add_or_ensure_same_typ(upd.var.name, upd.var.typ)
                source.visit_expr(upd.expr, check_expr_visitor)
        elif isinstance(node, source.NodeCall):
            for arg in node.args:
                source.visit_expr(arg, check_expr_visitor)
            for ret in node.rets:
                add_or_ensure_same_typ(ret.name, ret.typ)
        elif isinstance(node, source.NodeAssume | source.NodeCond | source.NodeAssert):
            source.visit_expr(node.expr, check_expr_visitor)
        elif not isinstance(node, source.NodeEmpty):
            assert_never(node)

        if lh := func.is_loop_header(n):
            for target in func.loops[lh].targets:
                add_or_ensure_same_typ(target.name, target.typ)

    assert len(var_types) == len(func.all_variables())


def validate(func: ghost_code.Function, dsa_func: dsa.Function) -> None:
    ensure_valid_variables(dsa_func)
    ensure_correspondence(func, dsa_func)
    ensure_valid_dsa(dsa_func)
    ensure_valid_contexts(dsa_func)
