from functools import reduce
from typing import Mapping, NamedTuple, NewType, Sequence, TypeAlias, cast, overload
from typing_extensions import assert_never
import dsa
from global_smt_variables import is_global_arbitrary, is_global_smt
import nip
import source
import ghost_code


VarName = NewType('VarName', str)
NodeOkName = NewType('NodeOkName', VarName)

APVar: TypeAlias = source.ExprVarT[VarName]


class InstructionAssume(NamedTuple):
    expr: source.ExprT[VarName]


class InstructionProve(NamedTuple):
    expr: source.ExprT[VarName]


Instruction = InstructionAssume | InstructionProve
Script = Sequence[InstructionAssume | InstructionProve]


class AssumeProveProg(NamedTuple):
    nodes_script: Mapping[NodeOkName, Script]

    entry: NodeOkName

    arguments: Sequence[APVar]
    # TODO: specify each assert with a specific error message


def node_ok_name(n: source.NodeName) -> NodeOkName:
    return NodeOkName(VarName(f'node_{n}_ok'))


def node_ok_ap_var(n: source.NodeName) -> APVar:
    return source.ExprVar(source.type_bool, VarName(node_ok_name(n)))


def convert_dsa_var_to_ap_var(var: dsa.Incarnation[source.ProgVarName | nip.GuardVarName]) -> VarName:
    return VarName(f'{var.base}~{var.inc}')


def convert_expr_var(expr: source.ExprVarT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> APVar:
    return source.ExprVar(expr.typ, name=convert_dsa_var_to_ap_var(expr.name))


# TODO: make sure mypy enforces this?
# TODO: rename to dsa_var_to_ap


@overload
def convert_expr_dsa_vars_to_ap(expr: source.ExprVarT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> source.ExprVarT[VarName]:
    ...


@overload
def convert_expr_dsa_vars_to_ap(expr: source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> source.ExprT[VarName]:
    ...


def convert_expr_dsa_vars_to_ap(expr: source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> source.ExprT[VarName]:
    if isinstance(expr, source.ExprNum):
        return expr
    elif isinstance(expr, source.ExprVar):
        return convert_expr_var(expr)
    elif isinstance(expr, source.ExprOp):
        return source.ExprOp(expr.typ, source.Operator(expr.operator), operands=tuple(
            convert_expr_dsa_vars_to_ap(operand) for operand in expr.operands
        ))
    elif isinstance(expr, source.ExprType | source.ExprSymbol):
        return expr
    elif isinstance(expr, source.ExprFunction):
        return source.ExprFunction(expr.typ, expr.function_name, [convert_expr_dsa_vars_to_ap(arg) for arg in expr.arguments], )
    assert_never(expr)


def make_assume(var: dsa.Var[source.ProgVarName | nip.GuardVarName], expr: source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> Instruction:
    """ Helper function to make things as readable as possible, we really don't want to get this wrong
    """
    lhs = source.ExprVar(var.typ, convert_dsa_var_to_ap_var(var.name))
    rhs = convert_expr_dsa_vars_to_ap(expr)
    eq = source.ExprOp(source.type_bool, source.Operator.EQUALS, (lhs, rhs))
    return InstructionAssume(eq)


# TODO: rename to base var to ap var
def prog_var_to_ap_var(v: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> APVar:
    return source.ExprVar(v.typ, VarName(v.name))


def get_loop_count_target_var(loop: source.Loop[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> source.ExprVarT[dsa.Incarnation[source.ProgVarName]]:
    for target in loop.targets:
        if target.name.base.startswith('loop#') and target.name.base.endswith('#count'):
            assert isinstance(target.name.base, source.ProgVarName)
            # mypy isn't smart enough to not need this cast
            return cast(source.ExprVarT[dsa.Incarnation[source.ProgVarName]], target)
    assert False, "loop doesn't have a loop a counter automatically inserted by the c parser"


def apply_incarnation_for_node(func: dsa.Function, n: source.NodeName, prog_var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> APVar:
    # if a variable isn't defined at that node, we use an arbitrary value
    #
    # THIS IS A POTENTIAL SOURCE OF UNSOUDNESS
    #
    # use case
    #     int a;
    #     for (int i = 0; i < 10; i++)
    #         // loop invariant: i >= 3 ==> a = 1
    #         //                 0 <= i <= 5
    #     {
    #         if (i == 2)
    #         {
    #             a = 1;
    #         }
    #         if (i == 5)
    #         {
    #             return a + 1;
    #         }
    #     }
    #     return 0;
    #
    # We have to prove the loop invariant holds on entry. However, there is no
    # available incarnation for 'a' on the node which jumps to the loop
    # header, yet the invariant depends on it. So we make a fresh variable
    # for it.
    #
    # Argument for correctness: if the loop invariant holds for an arbitrary value
    # of a, then it will hold for all concrete values during execution.

    if prog_var not in func.contexts[n]:
        return source.ExprVar(prog_var.typ, VarName(f'{prog_var.name}_arbitrary#node{n}'))
    return convert_expr_var(dsa.make_dsa_var(prog_var, func.contexts[n][prog_var]))


def make_assume_prove_script_for_node(func: dsa.Function, n: source.NodeName) -> Script:
    node = func.nodes[n]

    script: list[Instruction] = []
    if isinstance(node, source.NodeCond):
        # CondNode(expr, succ_then, succ_else)
        #     prove expr --> succ_then_ok
        #     prove not expr --> succ_else_ok
        cond = convert_expr_dsa_vars_to_ap(node.expr)

        if (n, node.succ_then) not in func.cfg.back_edges:
            script.append(InstructionProve(source.expr_implies(
                cond, node_ok_ap_var(node.succ_then))))
        if (n, node.succ_else) not in func.cfg.back_edges:
            script.append(InstructionProve(source.expr_implies(
                source.expr_negate(cond), node_ok_ap_var(node.succ_else))))

    elif isinstance(node, source.NodeBasic):
        # BasicNode(upds, succ)
        #     assume upd[i].lhs = upd[i].rhs    forall i
        #     prove succ_ok
        for upd in node.upds:
            script.append(make_assume(upd.var, upd.expr))

        # proves successors are correct, ignoring back edges
        if (n, node.succ) not in func.cfg.back_edges:
            script.append(InstructionProve(node_ok_ap_var(node.succ)))
    elif isinstance(node, source.NodeCall):
        # CallNode(func, args, rets, succ):
        #     prove func.pre(args)
        #     assume func.post(args, rets)
        #     prove succ_ok

        # TODO: pre and post condition
        # proves successors are correct, ignoring back edges
        if (n, node.succ) not in func.cfg.back_edges:
            script.append(InstructionProve(node_ok_ap_var(node.succ)))
    elif isinstance(node, source.NodeEmpty):
        # proves successors are correct, ignoring back edges
        if (n, node.succ) not in func.cfg.back_edges:
            script.append(InstructionProve(node_ok_ap_var(node.succ)))
    elif isinstance(node, source.NodeAssume):
        script.append(InstructionAssume(
            convert_expr_dsa_vars_to_ap(node.expr)))
        # proves successors are correct, ignoring back edges
        if (n, node.succ) not in func.cfg.back_edges:
            script.append(InstructionProve(node_ok_ap_var(node.succ)))
    elif isinstance(node, source.NodeAssert):
        if isinstance(node, ghost_code.NodePrecondObligationFnCall):

            # HACK: Massive hack, but save a whole lot of time
            cond = convert_expr_dsa_vars_to_ap(node.expr)
            conjs = list(source.expr_split_conjuncts(cond))
            assumptions: list[source.ExprT[VarName]] = []
            proof_obligations: list[source.ExprT[VarName]] = []
            for conj in conjs:

                is_equal_arbitrary = (isinstance(conj, source.ExprOp)
                                      and conj.operator == source.Operator.EQUALS
                                      and isinstance(conj.operands[1], source.ExprVar)
                                      and is_global_arbitrary(conj.operands[1].name.split('~')[0]))
                if is_equal_arbitrary:
                    assumptions.append(conj)
                else:
                    proof_obligations.append(conj)

            print(f"INFO: assert node {n} assumes:")
            for asmp in assumptions:
                print('  -', asmp)
            print("and proves")
            for pr in proof_obligations:
                print('  -', pr)

            def mk_conjs(xs): return reduce(   # type: ignore
                source.expr_and, xs)
            if assumptions != []:
                asm: source.ExprT[VarName] = mk_conjs(
                    assumptions)  # type: ignore
                script.append(InstructionAssume(asm))
            if proof_obligations != []:
                obl: source.ExprT[VarName] = mk_conjs(
                    proof_obligations)  # type: ignore
                script.append(InstructionProve(obl))

            if (n, node.succ) not in func.cfg.back_edges:
                script.append(InstructionProve(node_ok_ap_var(node.succ)))
            return script

        cond = convert_expr_dsa_vars_to_ap(node.expr)
        script.append(InstructionProve(source.expr_implies(
            source.expr_negate(cond), node_ok_ap_var(source.NodeNameErr))))
        if (n, node.succ) not in func.cfg.back_edges:
            script.append(InstructionProve(node_ok_ap_var(node.succ)))
    else:
        assert_never(node)

    return script


def condition_to_take_path(func: dsa.Function, path: source.Path) -> source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]:
    assert False, "TODO: remove dead code"
    cond: source.ExprT[dsa.Incarnation[source.ProgVarName |
                                       nip.GuardVarName]] = source.expr_true
    for i in range(len(path)):
        node = func.nodes[path[i]]
        if isinstance(node, source.NodeCond):
            # if the last node of the path is a conditional node, then the
            # node's condition doesn't add any condition to the path
            if not i + 1 < len(path):
                continue
            next_on_path = path[i+1]
            if node.succ_then == next_on_path:
                cond = source.expr_and(cond, node.expr)
            elif node.succ_else == next_on_path:
                cond = source.expr_and(cond, source.expr_negate(node.expr))
            else:
                assert False, "conditional node not jumping to following node"
        elif not isinstance(node, source.NodeBasic | source.NodeEmpty | source.NodeCall):
            assert_never(node)
    return cond


def make_prog(func: dsa.Function) -> AssumeProveProg:
    # don't need to keep DSA artifcats because we don't have pre conditions,
    # post conditions or loop invariants

    # NOTE: lots of room to eliminate SMT variable here
    #       a lot of blocks are just 'prove succ'

    nodes_script: dict[NodeOkName, Script] = {
        node_ok_name(source.NodeNameErr): [InstructionProve(source.ExprOp(source.type_bool, source.Operator.FALSE, ()))],
        # we don't have a post condition yet
        node_ok_name(source.NodeNameRet): [InstructionProve(source.ExprOp(source.type_bool, source.Operator.TRUE, ()))],
    }

    # traverse topologically to make the pretty printer nicer to read
    for n in func.traverse_topologically():
        if n in (source.NodeNameErr, source.NodeNameRet):
            continue

        nodes_script[node_ok_name(
            n)] = make_assume_prove_script_for_node(func, n)

    for script in nodes_script.values():
        assert all(ins.expr.typ == source.type_bool for ins in script)

    args = tuple(convert_expr_var(arg) for arg in func.signature.arguments)
    return AssumeProveProg(nodes_script=nodes_script, entry=node_ok_name(func.cfg.entry), arguments=args)


def pretty_instruction_ascii(ins: Instruction) -> str:
    if isinstance(ins, InstructionAssume):
        return f"assume {source.pretty_expr_ascii(ins.expr)}"
    elif isinstance(ins, InstructionProve):
        return f"prove {source.pretty_expr_ascii(ins.expr)}"
    assert_never(ins)


def pretty_print_prog(prog: AssumeProveProg) -> None:
    m = max(*(len(var.name) for script in prog.nodes_script.values()
              for ins in script for var in source.all_vars_in_expr(ins.expr)))
    m = max(m, len('X_ok'))
    print("Entry node:", prog.entry)
    print(f'{"X_ok".ljust(m)}: {source.pretty_type_ascii(source.type_bool)}')

    seen_vars: set[VarName] = set()
    for script in prog.nodes_script.values():
        for ins in script:
            for var in source.all_vars_in_expr(ins.expr):
                if var.name not in seen_vars:
                    print(
                        f'{var.name.ljust(m)}: {source.pretty_type_ascii(var.typ)}')
                    seen_vars.add(var.name)

    m = max(*(len(str(n)) for n in prog.nodes_script)) + 2
    for n in prog.nodes_script:
        print(f'{n}: '.ljust(m), end='')
        prefix = ' ' * m
        for i, instruction in enumerate(prog.nodes_script[n]):
            if i > 0:
                print(prefix, end='')
            print(pretty_instruction_ascii(instruction))
        # print(prefix + '=>',
        #       source.pretty_expr_ascii(apply_weakest_precondition(prog.nodes_script[n])))


def apply_weakest_precondition(script: Script) -> source.ExprT[VarName]:
    # A: wp(prove P, Q) = P && Q
    # B: wp(assume P, Q) = P --> Q
    # C: wp(S;T, Q) = wp(S, wp(T, Q))

    # there are only a few instruction per script (about <= 5)
    # so, we use recursion + copy because the performance won't matter
    # but the correctness is much clearer that way

    def wp_single(ins: Instruction, post: source.ExprT[VarName]) -> source.ExprT[VarName]:
        if isinstance(ins, InstructionProve):
            if post == source.expr_true:
                return ins.expr
            return source.expr_and(ins.expr, post)
        elif isinstance(ins, InstructionAssume):
            if post == source.expr_true:
                # a -> true is a tautology
                return source.expr_true
            return source.expr_implies(ins.expr, post)
        assert_never(ins)

    def wp(script: Script, post: source.ExprT[VarName]) -> source.ExprT[VarName]:
        if len(script) == 0:
            return post

        if len(script) == 1:
            return wp_single(script[0], post)

        # from C you can show `wp(S;T;R, Q) = wp(S, wp(T;R, Q)`
        # (; is associative, put the brackets are T;R)
        return wp([script[0]], wp(script[1:], post))

    return wp(script, source.expr_true)
