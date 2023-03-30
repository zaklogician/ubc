from __future__ import annotations
from enum import Enum
import subprocess
from typing import Any, Iterator, Literal, Mapping, Sequence, TypeAlias
from typing_extensions import NamedTuple, NewType, assert_never

import textwrap
import assume_prove
from global_smt_variables import PLATFORM_CONTEXT_BIT_SIZE
import source
import re
from utils import open_temp_file

SMTLIB = NewType("SMTLIB", str)

statically_infered_must_be_true = SMTLIB('true')

ops_to_smt: Mapping[source.Operator, SMTLIB] = {
    source.Operator.PLUS: SMTLIB("bvadd"),
    source.Operator.MINUS: SMTLIB("bvsub"),
    source.Operator.TIMES: SMTLIB("bvmul"),
    source.Operator.MODULUS: SMTLIB("bvurem"),
    source.Operator.DIVIDED_BY: SMTLIB("bvudiv"),
    source.Operator.BW_AND: SMTLIB("bvand"),
    source.Operator.BW_OR: SMTLIB("bvor"),
    source.Operator.BW_XOR: SMTLIB("bvxor"),
    source.Operator.AND: SMTLIB("and"),
    source.Operator.OR: SMTLIB("or"),
    source.Operator.IMPLIES: SMTLIB("=>"),
    source.Operator.EQUALS: SMTLIB("="),
    source.Operator.LESS: SMTLIB("bvult"),
    source.Operator.LESS_EQUALS: SMTLIB("bvule"),
    source.Operator.SIGNED_LESS: SMTLIB("bvslt"),
    source.Operator.SIGNED_LESS_EQUALS: SMTLIB("bvsle"),
    source.Operator.SHIFT_LEFT: SMTLIB("bvshl"),
    source.Operator.SHIFT_RIGHT: SMTLIB("bvlshr"),
    source.Operator.SIGNED_SHIFT_RIGHT: SMTLIB("bvashr"),
    source.Operator.NOT: SMTLIB("not"),
    source.Operator.BW_NOT: SMTLIB("bvnot"),
    source.Operator.TRUE: SMTLIB("true"),
    source.Operator.FALSE: SMTLIB("false"),
    source.Operator.IF_THEN_ELSE: SMTLIB("ite"),
    source.Operator.WORD_ARRAY_ACCESS: SMTLIB("select"),
    source.Operator.WORD_ARRAY_UPDATE: SMTLIB("store"),
    source.Operator.MEM_DOM: SMTLIB("mem-dom"),
    source.Operator.MEM_ACC: SMTLIB("mem-acc")
}

# memsort for rv64 native
MEM_SORT = SMTLIB('(Array (_ BitVec 61) (_ BitVec 64))')

BOOL = SMTLIB('Bool')

PMS = SMTLIB('PMS')
HTD = SMTLIB('HTD')

# 〈simple_symbol 〉 ::= a non-empty sequence of letters, digits and the characters
#                       + - / * = % ? ! . $ _ ~ & ˆ < > @ that does not start
#                       with a digit
RE_VALID_SMTLIB_SIMPLE_SYMBOL_STR = r'[a-zA-Z+\-/*=%?!.$_~<>@][a-zA-Z+\-/*=%?!.$_~<>@0-9]*'
RE_VALID_SMTLIB_SIMPLE_SYMBOL = re.compile(
    "^" + RE_VALID_SMTLIB_SIMPLE_SYMBOL_STR + "$")

Identifier = NewType('Identifier', str)


def word_array(typ: source.TypeWordArray) -> SMTLIB:
    return SMTLIB(f"(Array (_ BitVec {typ.index_bits}) (_ BitVec {typ.value_bits}))")


def identifier(illegal_name: assume_prove.VarName) -> Identifier:
    # '#' are disallowed in SMT
    #assert '@' not in illegal_name, "# are replaced with @, but some name already contains a @, which might result on conflicts"
    renamed = illegal_name.replace('#', '@')
    assert RE_VALID_SMTLIB_SIMPLE_SYMBOL.match(
        renamed), f"identifier {illegal_name!r} isn't valid"
    return Identifier(renamed)


class Logic(Enum):
    QF_ABV = 'QF_ABV'
    """ Quantifier free arrays and bit vectors """


class CmdSetLogic(NamedTuple):
    logic: Logic


class CmdDeclareFun(NamedTuple):
    symbol: Identifier
    arg_sorts: Sequence[source.Type]
    ret_sort: source.Type


class CmdAssert(NamedTuple):
    expr: source.ExprT[assume_prove.VarName]


class CmdCheckSat(NamedTuple):
    pass


class CmdDefineFun(NamedTuple):
    symbol: Identifier
    args: Sequence[source.ExprVarT[assume_prove.VarName]]
    ret_sort: source.Type
    term: source.ExprT[assume_prove.VarName]


class CmdDeclareSort(NamedTuple):
    symbol: Identifier
    arity: int


class CmdComment(NamedTuple):
    comment: str


EmptyLine = CmdComment('')

Cmd = CmdDeclareFun | CmdDefineFun | CmdAssert | CmdCheckSat | CmdComment | CmdSetLogic | CmdDeclareSort


ModelResponse: TypeAlias = CmdDefineFun


class CheckSatResponse(Enum):
    UNSAT = SMTLIB("unsat")
    SAT = SMTLIB("sat")
    UNKNOWN = SMTLIB("unknown")


GetModelResponse = Sequence[ModelResponse]
Response = CheckSatResponse | GetModelResponse
Responses = Sequence[Response]


def smt_bitvec_of_size(val: int, size: int) -> SMTLIB:
    assert val >= 0
    assert size > 0
    return SMTLIB(f"(_ bv{val} {size})")


def smt_extract(msb_idx: int, lsb_idx: int, expected_num_bits: int, lhs: source.ExprT[assume_prove.VarName]) -> SMTLIB:
    """
    msb_idx: most significant bit index
    lsb_idx: least significant bit index
    expected_num_bits is just used for safety

    All function symbols with declaration of the form

        ((_ extract i j) (_ BitVec m) (_ BitVec n))

    where
    - i, j, m, n are numerals
    - m > i ≥ j ≥ 0,
    - n = i - j + 1
    """

    assert isinstance(lhs.typ, source.TypeBitVec)
    assert lhs.typ.size > msb_idx >= lsb_idx >= 0
    assert expected_num_bits == msb_idx - lsb_idx + 1

    return SMTLIB(f"((_ extract {msb_idx} {lsb_idx}) {emit_expr(lhs)})")


def smt_zero_extend(num_extra_bits: int, lhs: source.ExprT[assume_prove.VarName]) -> SMTLIB:
    # ((_ zero_extend 0) t) stands for t
    # ((_ zero_extend i) t) abbreviates (concat ((_ repeat i) #b0) t)

    assert num_extra_bits >= 0
    return SMTLIB(f"((_ zero_extend {num_extra_bits}) {emit_expr(lhs)})")


def smt_sign_extend(num_extra_bits: int, lhs: source.ExprT[assume_prove.VarName]) -> SMTLIB:
    # ((_ sign_extend 0) t) stands for t
    # ((_ sign_extend i) t) abbreviates
    #   (concat ((_ repeat i) ((_ extract |m-1| |m-1|) t)) t)

    assert num_extra_bits >= 0
    return SMTLIB(f"((_ sign_extend {num_extra_bits}) {emit_expr(lhs)})")


def emit_num_with_correct_type(expr: source.ExprNumT) -> SMTLIB:
    if isinstance(expr.typ, source.TypeBitVec):
        assert - \
            2 ** expr.typ.size <= expr.num < 2 ** expr.typ.size, f"{expr.num=} doesn't fit in the type {expr.typ=}"
        if expr.num >= 0:
            num = expr.num
        else:
            num = 2 ** 32 + expr.num
        return smt_bitvec_of_size(val=num, size=expr.typ.size)
    assert False, f"{expr} not supported"


def emit_bitvec_cast(target_typ: source.TypeBitVec, operator: Literal[source.Operator.WORD_CAST, source.Operator.WORD_CAST_SIGNED], lhs: source.ExprT[assume_prove.VarName]) -> SMTLIB:
    assert isinstance(lhs.typ, source.TypeBitVec)
    if lhs.typ.size == target_typ.size:
        return emit_expr(lhs)

    if target_typ.size < lhs.typ.size:
        # extract the bottom <target_type.size> bits
        return smt_extract(msb_idx=target_typ.size - 1, lsb_idx=0, expected_num_bits=target_typ.size, lhs=lhs)

    assert lhs.typ.size < target_typ.size
    if operator == source.Operator.WORD_CAST:
        return smt_zero_extend(num_extra_bits=target_typ.size - lhs.typ.size, lhs=lhs)
    elif operator == source.Operator.WORD_CAST_SIGNED:
        return smt_sign_extend(num_extra_bits=target_typ.size - lhs.typ.size, lhs=lhs)

    assert_never(operator)


def emit_expr(expr: source.ExprT[assume_prove.VarName]) -> SMTLIB:
    if isinstance(expr, source.ExprNum):
        return emit_num_with_correct_type(expr)
    elif isinstance(expr, source.ExprOp):

        # mypy isn't smart enough to understand `in`, so we split the iffs
        if expr.operator == source.Operator.WORD_CAST:
            assert len(expr.operands) == 1
            assert isinstance(expr.typ, source.TypeBitVec)
            return emit_bitvec_cast(expr.typ, source.Operator.WORD_CAST, expr.operands[0])

        if expr.operator == source.Operator.WORD_CAST_SIGNED:
            assert len(expr.operands) == 1
            assert isinstance(expr.typ, source.TypeBitVec)
            return emit_bitvec_cast(expr.typ, source.Operator.WORD_CAST_SIGNED, expr.operands[0])

        if expr.operator in source.nulary_operators:
            return SMTLIB(ops_to_smt[expr.operator])

        if expr.operator is source.Operator.P_ALIGN_VALID:
            assert len(expr.operands) == 2
            typ, val = expr.operands
            assert isinstance(typ, source.ExprType), typ
            if isinstance(val, source.ExprSymbol):
                return statically_infered_must_be_true
            raise NotImplementedError(
                "PAlignValid for non symbols isn't supported")
        if expr.operator is source.Operator.MEM_ACC:
            assert len(expr.operands) == 2
            mem, symb_or_addr = expr.operands
            if not isinstance(symb_or_addr, source.ExprSymbol):
                raise NotImplementedError(
                    "MemAcc for non symbols isn't supported")

            as_fn_call = f"{symb_or_addr.name}"
            return SMTLIB(f"({ops_to_smt[expr.operator]} {emit_expr(mem)} {as_fn_call})")

        return SMTLIB(f'({ops_to_smt[expr.operator]} {" ".join(emit_expr(op) for op in expr.operands)})')
    elif isinstance(expr, source.ExprVar):
        return SMTLIB(f'{identifier(expr.name)}')
    elif isinstance(expr, source.ExprSymbol | source.ExprType):
        assert False, "what do i do with this?"
    elif isinstance(expr, source.ExprFunction):
        if len(expr.arguments) == 0:
            return SMTLIB(f'{expr.function_name}')
        return SMTLIB(f'({expr.function_name} {" ".join(emit_expr(arg) for arg in expr.arguments)})')
    assert_never(expr)


def emit_sort(typ: source.Type) -> SMTLIB:
    if isinstance(typ, source.TypeBuiltin):
        if typ.builtin is source.Builtin.BOOL:
            return BOOL
        elif typ.builtin is source.Builtin.MEM:
            return MEM_SORT
        elif typ.builtin is source.Builtin.PMS:
            return PMS
        elif typ.builtin is source.Builtin.HTD:
            return HTD
    elif isinstance(typ, source.TypeBitVec):
        return SMTLIB(f'(_ BitVec {typ.size})')
    elif isinstance(typ, source.TypeWordArray):
        return word_array(typ)

    assert False, f'unhandled sort {typ}'


def emit_cmd(cmd: Cmd) -> SMTLIB:
    if isinstance(cmd, CmdDeclareFun):
        # (declare-fun func_name (T1 T2 ...) T)
        arg_sorts = " ".join(emit_sort(s) for s in cmd.arg_sorts)
        ret_sort = emit_sort(cmd.ret_sort)
        return SMTLIB(f'(declare-fun {cmd.symbol} ({arg_sorts}) {ret_sort})')
    elif isinstance(cmd, CmdAssert):
        return SMTLIB(f"(assert {emit_expr(cmd.expr)})")
    elif isinstance(cmd, CmdCheckSat):
        return SMTLIB(f"(check-sat)")
    elif isinstance(cmd, CmdDefineFun):
        # (define-fun func_name ((a T1) (b T2) ...) T (body))

        assert RE_VALID_SMTLIB_SIMPLE_SYMBOL.match(
            cmd.symbol), f"function name {cmd.symbol!r} isn't valid"
        for arg in cmd.args:
            assert RE_VALID_SMTLIB_SIMPLE_SYMBOL.match(
                cmd.symbol), f"argument {cmd.symbol!r} isn't valid"

        args = ' '.join(
            f'({identifier(arg.name)} {emit_sort(arg.typ)})' for arg in cmd.args)
        return SMTLIB(f"(define-fun {cmd.symbol} ({args}) {emit_sort(cmd.ret_sort)} {emit_expr(cmd.term)})")
    elif isinstance(cmd, CmdComment):
        if cmd.comment == '':
            return SMTLIB('')
        return SMTLIB('; ' + cmd.comment)
    elif isinstance(cmd, CmdSetLogic):
        return SMTLIB(f'(set-logic {cmd.logic.value})')
    elif isinstance(cmd, CmdDeclareSort):
        return SMTLIB(f"(declare-sort {cmd.symbol} {cmd.arity})")
    assert_never(cmd)


def cmd_assert_eq(name: assume_prove.VarName, rhs: source.ExprT[assume_prove.VarName]) -> Cmd:
    return CmdAssert(source.ExprOp(rhs.typ, source.Operator.EQUALS, (source.ExprVar(rhs.typ, name), rhs)))


def merge_smtlib(it: Iterator[SMTLIB]) -> SMTLIB:
    return SMTLIB('\n'.join(it))


def emit_prelude() -> Sequence[Cmd]:
    pms = CmdDeclareSort(Identifier(str(PMS)), 0)
    htd = CmdDeclareSort(Identifier(str(HTD)), 0)
    mem_var = source.ExprVar(
        typ=source.type_mem, name=assume_prove.VarName("mem"))
    addr_var = source.ExprVar(typ=source.type_word61,
                              name=assume_prove.VarName("addr"))
    mem_acc = CmdDefineFun(Identifier(str("mem-acc")), [mem_var, addr_var], source.type_word64, source.ExprOp(
        typ=source.type_word64, operands=(mem_var, addr_var), operator=source.Operator.WORD_ARRAY_ACCESS))

    # DEADLINE HACK
    sel4cp_internal_badge = CmdDeclareFun(Identifier(
        str("badge")), arg_sorts=[], ret_sort=source.type_word61)
    prelude: Sequence[Cmd] = [pms, htd, mem_acc, sel4cp_internal_badge]
    return prelude


def make_smtlib(p: assume_prove.AssumeProveProg, debug: bool = False) -> SMTLIB:
    emited_identifiers: set[Identifier] = set()
    emited_variables: set[assume_prove.VarName] = set()

    # don't insert logic because hack below
    cmds: list[Cmd] = []
    cmds.extend(emit_prelude())

    # emit all auxilary variable declaration (declare-fun node_x_ok () Bool)
    for node_ok_name in p.nodes_script:
        cmds.append(CmdDeclareFun(identifier(
            node_ok_name), (), source.type_bool))
        emited_identifiers.add(identifier(node_ok_name))
        emited_variables.add(node_ok_name)

    cmds.append(EmptyLine)

    # emit all arguments
    for arg in p.arguments:
        cmds.append(CmdDeclareFun(identifier(arg.name), (), arg.typ))
        emited_identifiers.add(identifier(arg.name))
        emited_variables.add(arg.name)

    # emit all variable declaration (declare-fun y () <sort>)
    for script in p.nodes_script.values():
        for ins in script:
            for var in source.all_vars_in_expr(ins.expr):
                iden = identifier(var.name)
                if iden not in emited_identifiers:
                    cmds.append(CmdDeclareFun(iden, (), var.typ))
                    emited_identifiers.add(iden)
                    emited_variables.add(var.name)

    cmds.append(EmptyLine)

    err_num: int = 0

    def replace_fn(var: source.ExprVarT[assume_prove.VarName]) -> source.ExprT[assume_prove.VarName]:
        nonlocal err_num
        if var.name == 'node_Err_ok':
            ret = source.ExprVar(
                var.typ, assume_prove.VarName(f'node_Err_ok_{err_num}'))
            err_num += 1
            return ret
        return var

    node_ok_cmds = []
    # emit all assertions from nodes (node_x_ok = wp(x))
    for node_ok_name, script in p.nodes_script.items():
        when_not_debug = assume_prove.apply_weakest_precondition(script)
        when_debug = source.convert_expr_vars(replace_fn, when_not_debug)
        expr = when_debug if debug else when_not_debug
        node_ok_cmds.append(cmd_assert_eq(node_ok_name, expr))

    if debug:
        for i in range(0, err_num):
            iden = identifier(assume_prove.VarName(f'node_Err_ok_{i}'))
            cmds.append(CmdDefineFun(
                iden, (), source.type_bool, source.expr_true))

    cmds.append(EmptyLine)
    cmds = cmds + node_ok_cmds

    cmds.append(CmdCheckSat())
    cmds.append(CmdAssert(source.expr_negate(
        source.ExprVar(source.type_bool, p.entry))))

    cmds.append(CmdCheckSat())

    # HACK: include sel4cp prelude
    raw_prelude = SMTLIB(
        '(set-logic QF_ABV)\n'
        '(define-fun node_Err_okd () Bool true)\n'
        f'(declare-fun ghost_arbitrary_1 () (_ BitVec {PLATFORM_CONTEXT_BIT_SIZE}))'
    )
    with open('./sel4cp-prelude.smt2') as f:
        raw_prelude = SMTLIB(f.read() + '\n\n')
    with open('./sel4cp-manual-prelude.smt2') as f:
        raw_prelude = SMTLIB(raw_prelude + f.read() + '\n\n')

    clean_smt = merge_smtlib(emit_cmd(cmd) for cmd in cmds)
    return SMTLIB(raw_prelude + clean_smt)


class CheckSatResult(Enum):
    # TODO: unknown
    UNSAT = 'unsat'
    SAT = 'sat'


def send_smtlib_to_z3(smtlib: SMTLIB) -> Iterator[CheckSatResult]:
    """ Send command to an smt solver and returns a boolean per (check-sat)
    """

    # print("sending SMTLIB:")
    # for i, line in enumerate(emit_cmd(cmd) for cmd in cmds):
    #     print(f'{str(i+1).rjust(int(math.log10(len(cmds)) + 1))} | {line}')

    # p = subprocess.Popen(["z3", "-version"])
    # err = p.wait()
    # if err:
    #     raise ValueError("z3 not found")

    with open_temp_file(suffix='.smt2') as (f, fullpath):
        f.write(smtlib)
        f.close()

        p = subprocess.Popen(["z3", "-file:" + fullpath],
                             stderr=subprocess.PIPE, stdout=subprocess.PIPE)
        p.wait()

    assert p.stderr is not None
    assert p.stdout is not None

    if p.returncode != 0:
        print("stderr:")
        print(textwrap.indent(p.stdout.read().decode('utf-8'), '   '))
        print("Return code:", p.returncode)
        return

    lines = p.stdout.read().splitlines()
    for ln in lines:
        yield CheckSatResult(ln.decode('utf-8'))


class VerificationResult(Enum):
    OK = 'ok'
    FAIL = 'fail'
    INCONSTENT = 'inconsistent'


def parse_sats(sats: Sequence[CheckSatResult]) -> VerificationResult:
    assert len(sats) == 2

    if sats[0] != CheckSatResult.SAT:
        return VerificationResult.INCONSTENT
    elif sats[1] != CheckSatResult.UNSAT:
        return VerificationResult.FAIL

    return VerificationResult.OK
