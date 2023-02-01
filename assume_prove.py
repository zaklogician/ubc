from typing import Mapping, NamedTuple, NewType, Sequence, TypeAlias
from typing_extensions import assert_never
import dsa
import source


VarName = NewType('VarName', str)
NodeOkName = NewType('NodeOkName', VarName)

APVar: TypeAlias = source.ExprVarT[VarName]


class InstructionAssume(NamedTuple):
    expr: source.ExprT[VarName]


class InstructionProve(NamedTuple):
    expr: source.ExprT[VarName]


Instruction = InstructionAssume | InstructionProve
Script = Sequence[InstructionAssume | InstructionProve]

LoopInvariantFunctionName = NewType(
    'LoopInvariantFunctionName', source.FunctionName)


class FunctionDefinition(NamedTuple):
    """ This is an *smt* function, not a C function """
    name: source.FunctionName
    arguments: Sequence[APVar]
    return_typ: source.Type
    body: source.ExprT[VarName]


class AssumeProveProg(NamedTuple):
    nodes_script: Mapping[NodeOkName, Script]

    entry: NodeOkName

    function_definitions: Sequence[FunctionDefinition]

    # TODO: specify each assert with a specific error message


def node_ok_name(n: source.NodeName) -> NodeOkName:
    return NodeOkName(VarName(f'node_{n}_ok'))


def node_ok_ap_var(n: source.NodeName) -> APVar:
    return source.ExprVar(source.type_bool, VarName(node_ok_name(n)))


def convert_dsa_var_to_ap_var(var: dsa.VarName) -> VarName:
    return VarName(f'{var.prog}~{var.inc}')


def convert_expr_var(expr: source.ExprVarT[dsa.VarName]) -> APVar:
    return source.ExprVar(expr.typ, name=convert_dsa_var_to_ap_var(expr.name))


def convert_expr_dsa_vars_to_ap(expr: source.ExprT[dsa.VarName]) -> source.ExprT[VarName]:
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


def make_assume(var: dsa.Var, expr: source.ExprT[dsa.VarName]) -> Instruction:
    """ Helper function to make things as readable as possible, we really don't want to get this wrong
    """
    lhs = source.ExprVar(var.typ, convert_dsa_var_to_ap_var(var.name))
    rhs = convert_expr_dsa_vars_to_ap(expr)
    eq = source.ExprOp(source.type_bool, source.Operator.EQUALS, (lhs, rhs))
    return InstructionAssume(eq)


def make_loop_invariant_function_name(loop_header: source.LoopHeaderName) -> LoopInvariantFunctionName:
    return LoopInvariantFunctionName(source.FunctionName(f'loop_invariant@{loop_header}'))


def prog_var_to_ap_var(v: source.ProgVar) -> APVar:
    return source.ExprVar(v.typ, VarName(v.name))


def get_loop_invariant_function(func: source.Function[dsa.VarName], loop_header: source.LoopHeaderName) -> FunctionDefinition:
    # TODO: there is no point rebuilding the same object multiple times
    #       hint to use an AP builder
    name = make_loop_invariant_function_name(loop_header)
    args = [prog_var_to_ap_var(dsa.get_prog_var(target))
            for target in func.loops[loop_header].targets]
    # emit loop invariant as true (ie. doesn't do anything)
    return FunctionDefinition(name=name, arguments=args, return_typ=source.type_bool, body=source.expr_true)


def apply_incarnation_for_node(func: dsa.Function, n: source.NodeName, prog_var: source.ProgVar) -> APVar:
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

    # 1. assume invariant if we are a loop header
    # 2. emit node specific assume/prove instruction
    # 3. if we jump to a loop header, prove that it's loop invariant is maintained

    script: list[Instruction] = []
    if loop_header := func.is_loop_header(n):
        # we get to assume the loop invariant
        invariant = get_loop_invariant_function(func, loop_header)

        args = [convert_expr_var(target)
                for target in func.loops[loop_header].targets]
        script.append(InstructionAssume(source.ExprFunction(
            invariant.return_typ, invariant.name, args)))

    if isinstance(node, source.NodeCond):
        # CondNode(expr, succ_then, succ_else)
        #     prove expr --> succ_then_ok
        #     prove not expr --> succ_else_ok
        cond = convert_expr_dsa_vars_to_ap(node.expr)

        assert not any(func.is_loop_header(succ)
                       for succ in func.cfg.all_succs[n])
        assert not func.is_loop_latch(
            n), "TODO: handle conditional nodes that are loop latches (recall that we remove back edges)"

        script.append(InstructionProve(source.expr_implies(
            cond, node_ok_ap_var(node.succ_then))))
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
    else:
        assert_never(node)

    for succ in func.cfg.all_succs[n]:
        if loop_header := func.is_loop_header(succ):
            # we need to prove that the loop invariant holds
            invariant = get_loop_invariant_function(func, loop_header)

            # use the incarnation at node n
            args = [
                apply_incarnation_for_node(func, n, dsa.get_prog_var(arg)) for arg in func.loops[loop_header].targets]

            script.append(InstructionProve(source.expr_implies(source.expr_negate(source.ExprFunction(
                invariant.return_typ, invariant.name, args)), node_ok_ap_var(source.NodeNameErr))))

    return script


def condition_to_take_path(func: dsa.Function, path: source.Path) -> source.ExprT[dsa.VarName]:
    cond: source.ExprT[dsa.VarName] = source.expr_true
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

    function_definitions = [get_loop_invariant_function(
        func, loop_header) for loop_header in func.loops]
    return AssumeProveProg(nodes_script=nodes_script, entry=node_ok_name(func.cfg.entry), function_definitions=function_definitions)


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
