from typing import Mapping, NamedTuple, NewType, Sequence, TypeAlias
from typing_extensions import assert_never
from dsa import DSAVar, DSAVarName
from source import ExprNum, ExprVar, ExprOp, ExprType, ExprSymbol, NodeBasic, NodeCall, NodeCond, NodeEmpty, NodeName, NodeNameErr, NodeNameRet, Operator, all_vars_in_expr, assigned_variables_in_node, expr_and, expr_implies, expr_negate, pretty_expr_ascii, type_bool, Expr, Node, Type, expr_true, Function

APVarName = NewType('APVarName', str)

APVar: TypeAlias = ExprVar[APVarName]


class APInstructionAssume(NamedTuple):
    expr: Expr[APVarName]


class APInstructionProve(NamedTuple):
    expr: Expr[APVarName]


NodeOkName = NewType('NodeOkName', APVarName)
APInstruction = APInstructionAssume | APInstructionProve

AssumeProveScript = Sequence[APInstructionAssume | APInstructionProve]


def node_ok_name(n: NodeName) -> NodeOkName:
    return NodeOkName(APVarName(f'node_{n}_ok'))


def node_ok_ap_var(n: NodeName) -> ExprVar[APVarName]:
    return ExprVar(type_bool, APVarName(node_ok_name(n)))


def convert_dsa_var_to_ap_var(var: DSAVarName) -> APVarName:
    return APVarName(f'{var.prog}~{var.inc}')


def convert_expr_dsa_vars_to_ap(expr: Expr[DSAVarName]) -> Expr[APVarName]:
    if isinstance(expr, ExprNum):
        return expr
    elif isinstance(expr, ExprVar):
        return ExprVar(expr.typ, name=convert_dsa_var_to_ap_var(expr.name))
    elif isinstance(expr, ExprOp):
        return ExprOp(expr.typ, Operator(expr.operator), operands=tuple(
            convert_expr_dsa_vars_to_ap(operand) for operand in expr.operands
        ))
    elif isinstance(expr, ExprType | ExprSymbol):
        return expr
    assert_never(expr)


def ap_assume(var: DSAVar, expr: Expr[DSAVarName]) -> APInstruction:
    """ Helper function to make things as readable as possible, we really don't want to get this wrong
    """
    lhs = ExprVar(var.typ, convert_dsa_var_to_ap_var(var.name))
    rhs = convert_expr_dsa_vars_to_ap(expr)
    eq = ExprOp(type_bool, Operator.EQUALS, (lhs, rhs))
    return APInstructionAssume(eq)


def ap_prove(expr: Expr[APVarName]) -> APInstruction:
    return APInstructionProve(expr)


def make_assume_prove_script_for_node(node: Node[DSAVarName]) -> AssumeProveScript:
    # TODO: loop invariants

    if isinstance(node, NodeBasic):
        # BasicNode(upds, succ)
        #     assume upd[i].lhs = upd[i].rhs    forall i
        #     prove succ_ok
        script = []
        for upd in node.upds:
            script.append(ap_assume(upd.var, upd.expr))
        script.append(APInstructionProve(node_ok_ap_var(node.succ)))
        return script
    elif isinstance(node, NodeCond):
        # CondNode(expr, succ_then, succ_else)
        #     prove expr --> succ_then_ok
        #     prove not expr --> succ_else_ok
        cond = convert_expr_dsa_vars_to_ap(node.expr)
        return [
            ap_prove(expr_implies(cond, node_ok_ap_var(node.succ_then))),
            ap_prove(expr_implies(expr_negate(cond),
                                  node_ok_ap_var(node.succ_else)))
        ]
    elif isinstance(node, NodeCall):
        # CallNode(func, args, rets, succ):
        #     prove func.pre(args)
        #     assume func.post(args, rets)
        #     prove succ_ok

        # TODO: pre and post condition
        return [ap_prove(node_ok_ap_var(node.succ))]
    elif isinstance(node, NodeEmpty):
        return [ap_prove(node_ok_ap_var(node.succ))]

    assert_never(node)


class AssumeProveProg(NamedTuple):
    nodes_script: Mapping[NodeOkName, AssumeProveScript]

    entry: NodeOkName

    # TODO: include path that lead to use of non initialized variables


def make_assume_prove_prog(func: Function[DSAVarName]) -> AssumeProveProg:
    # don't need to keep DSA artifcats because we don't have pre conditions,
    # post conditions or loop invariants

    # NOTE: lots of room to eliminate SMT variable here
    #       a lot of blocks are just 'prove succ'

    nodes_script: dict[NodeOkName, AssumeProveScript] = {
        node_ok_name(NodeNameErr): [APInstructionProve(ExprOp(type_bool, Operator.FALSE, ()))],
        # we don't have a post condition yet
        node_ok_name(NodeNameRet): [APInstructionProve(ExprOp(type_bool, Operator.TRUE, ()))],
    }

    # traverse topologically to make the pretty printer nicer to read
    for n in func.traverse_topologically():
        if n in (NodeNameErr, NodeNameRet):
            continue

        nodes_script[node_ok_name(n)] = make_assume_prove_script_for_node(
            func.nodes[n])
        for var in assigned_variables_in_node(func, n):
            ap_var_name = convert_dsa_var_to_ap_var(var.name)

    for script in nodes_script.values():
        assert all(ins.expr.typ == type_bool for ins in script)

    return AssumeProveProg(nodes_script=nodes_script, entry=node_ok_name(func.cfg.entry))


def ap_pretty_instruction_ascii(ins: APInstruction) -> str:
    if isinstance(ins, APInstructionAssume):
        return f"assume {pretty_expr_ascii(ins.expr)}"
    elif isinstance(ins, APInstructionProve):
        return f"prove {pretty_expr_ascii(ins.expr)}"
    assert_never(ins)


def ap_pretty_print_prog(prog: AssumeProveProg) -> None:
    print(f'X_ok:', type_bool)
    seen_vars: set[APVarName] = set()
    for script in prog.nodes_script.values():
        for ins in script:
            for var in all_vars_in_expr(ins.expr):
                if var.name not in seen_vars:
                    print(f'{var.name}: {var.typ}')
                    seen_vars.add(var.name)

    for n in prog.nodes_script:
        print(f'{n}: '.ljust(10), end='')
        prefix = ' ' * 10
        for i, instruction in enumerate(prog.nodes_script[n]):
            if i > 0:
                print(prefix, end='')
            print(ap_pretty_instruction_ascii(instruction))
        print(prefix + '=>',
              pretty_expr_ascii(apply_weakest_precondition(prog.nodes_script[n])))


def apply_weakest_precondition(script: AssumeProveScript) -> Expr[APVarName]:
    # A: wp(prove P, Q) = P && Q
    # B: wp(assume P, Q) = P --> Q
    # C: wp(S;T, Q) = wp(S, wp(T, Q))

    # there are only a few instruction per script (about <= 5)
    # so, we use recursion + copy because the performance won't matter
    # but the correctness is much clearer that way

    def wp_single(ins: APInstruction, post: Expr[APVarName]) -> Expr[APVarName]:
        if isinstance(ins, APInstructionProve):
            if post == expr_true:
                return ins.expr
            return expr_and(ins.expr, post)
        elif isinstance(ins, APInstructionAssume):
            if post == expr_true:
                # a -> true is a tautology
                return expr_true
            return expr_implies(ins.expr, post)
        assert_never(ins)

    def wp(script: AssumeProveScript, post: Expr[APVarName]) -> Expr[APVarName]:
        if len(script) == 0:
            return post

        if len(script) == 1:
            return wp_single(script[0], post)

        # from C you can show `wp(S;T;R, Q) = wp(S, wp(T;R, Q)`
        # (; is associative, put the brackets are T;R)
        return wp([script[0]], wp(script[1:], post))

    return wp(script, expr_true)
