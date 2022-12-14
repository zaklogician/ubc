from typing import Mapping, NamedTuple, NewType, Sequence, TypeAlias
from typing_extensions import assert_never
import dsa
import source


VarName = NewType('VarName', str)
NodeOkName = NewType('NodeOkName', VarName)

APVar: TypeAlias = source.ExprVar[VarName]


class InstructionAssume(NamedTuple):
    expr: source.Expr[VarName]


class InstructionProve(NamedTuple):
    expr: source.Expr[VarName]


Instruction = InstructionAssume | InstructionProve
Script = Sequence[InstructionAssume | InstructionProve]


class AssumeProveProg(NamedTuple):
    nodes_script: Mapping[NodeOkName, Script]

    entry: NodeOkName

    # TODO: include path that lead to use of non initialized variables
    # TODO: specify each assert with a specific error message
    # assertions: Assertions


def node_ok_name(n: source.NodeName) -> NodeOkName:
    return NodeOkName(VarName(f'node_{n}_ok'))


def node_ok_ap_var(n: source.NodeName) -> source.ExprVar[VarName]:
    return source.ExprVar(source.type_bool, VarName(node_ok_name(n)))


def convert_dsa_var_to_ap_var(var: dsa.VarName) -> VarName:
    return VarName(f'{var.prog}~{var.inc}')


def convert_expr_dsa_vars_to_ap(expr: source.Expr[dsa.VarName]) -> source.Expr[VarName]:
    if isinstance(expr, source.ExprNum):
        return expr
    elif isinstance(expr, source.ExprVar):
        return source.ExprVar(expr.typ, name=convert_dsa_var_to_ap_var(expr.name))
    elif isinstance(expr, source.ExprOp):
        return source.ExprOp(expr.typ, source.Operator(expr.operator), operands=tuple(
            convert_expr_dsa_vars_to_ap(operand) for operand in expr.operands
        ))
    elif isinstance(expr, source.ExprType | source.ExprSymbol):
        return expr
    assert_never(expr)


def make_assume(var: dsa.Var, expr: source.Expr[dsa.VarName]) -> Instruction:
    """ Helper function to make things as readable as possible, we really don't want to get this wrong
    """
    lhs = source.ExprVar(var.typ, convert_dsa_var_to_ap_var(var.name))
    rhs = convert_expr_dsa_vars_to_ap(expr)
    eq = source.ExprOp(source.type_bool, source.Operator.EQUALS, (lhs, rhs))
    return InstructionAssume(eq)


def make_prove(expr: source.Expr[VarName]) -> Instruction:
    return InstructionProve(expr)


def make_assume_prove_script_for_node(node: source.Node[dsa.VarName]) -> Script:
    # TODO: loop invariants

    if isinstance(node, source.NodeBasic):
        # BasicNode(upds, succ)
        #     assume upd[i].lhs = upd[i].rhs    forall i
        #     prove succ_ok
        script = []
        for upd in node.upds:
            script.append(make_assume(upd.var, upd.expr))
        script.append(InstructionProve(node_ok_ap_var(node.succ)))
        return script
    elif isinstance(node, source.NodeCond):
        # CondNode(expr, succ_then, succ_else)
        #     prove expr --> succ_then_ok
        #     prove not expr --> succ_else_ok
        cond = convert_expr_dsa_vars_to_ap(node.expr)
        return [
            make_prove(source.expr_implies(
                cond, node_ok_ap_var(node.succ_then))),
            make_prove(source.expr_implies(source.expr_negate(cond),
                                           node_ok_ap_var(node.succ_else)))
        ]
    elif isinstance(node, source.NodeCall):
        # CallNode(func, args, rets, succ):
        #     prove func.pre(args)
        #     assume func.post(args, rets)
        #     prove succ_ok

        # TODO: pre and post condition
        return [make_prove(node_ok_ap_var(node.succ))]
    elif isinstance(node, source.NodeEmpty):
        return [make_prove(node_ok_ap_var(node.succ))]

    assert_never(node)


def make_prog(func: source.Function[dsa.VarName]) -> AssumeProveProg:
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

        nodes_script[node_ok_name(n)] = make_assume_prove_script_for_node(
            func.nodes[n])
        for var in source.assigned_variables_in_node(func, n):
            ap_var_name = convert_dsa_var_to_ap_var(var.name)

    for script in nodes_script.values():
        assert all(ins.expr.typ == source.type_bool for ins in script)

    return AssumeProveProg(nodes_script=nodes_script, entry=node_ok_name(func.cfg.entry))


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
        print(prefix + '=>',
              source.pretty_expr_ascii(apply_weakest_precondition(prog.nodes_script[n])))


def apply_weakest_precondition(script: Script) -> source.Expr[VarName]:
    # A: wp(prove P, Q) = P && Q
    # B: wp(assume P, Q) = P --> Q
    # C: wp(S;T, Q) = wp(S, wp(T, Q))

    # there are only a few instruction per script (about <= 5)
    # so, we use recursion + copy because the performance won't matter
    # but the correctness is much clearer that way

    def wp_single(ins: Instruction, post: source.Expr[VarName]) -> source.Expr[VarName]:
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

    def wp(script: Script, post: source.Expr[VarName]) -> source.Expr[VarName]:
        if len(script) == 0:
            return post

        if len(script) == 1:
            return wp_single(script[0], post)

        # from C you can show `wp(S;T;R, Q) = wp(S, wp(T;R, Q)`
        # (; is associative, put the brackets are T;R)
        return wp([script[0]], wp(script[1:], post))

    return wp(script, source.expr_true)
