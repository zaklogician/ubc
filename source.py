from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, unique
from typing import Any, Callable, Collection, Generic, Iterator, Mapping, NewType, Sequence, Set, TypeAlias, TypeVar
from typing_extensions import assert_never

import syntax

ProgVarName = NewType('ProgVarName', str)
VarNameKind = TypeVar("VarNameKind")
TypeKind = TypeVar("TypeKind")

NodeName = NewType('NodeName', str)
NodeNameErr = NodeName('Err')
NodeNameRet = NodeName('Ret')

Path: TypeAlias = tuple[NodeName, ...]


@dataclass(frozen=True, order=True)
class TypeStruct:
    name: str


@dataclass(frozen=True, order=True)
class TypeBitVec:
    """ Synonym for TypeWord
    """
    size: int


@dataclass(frozen=True, order=True)
class TypeArray:
    element_typ: Type
    size: int


@dataclass(frozen=True, order=True)
class TypePtr:
    pointee_type: Type


@dataclass(frozen=True)
class TypeFloatingPoint:
    exp_bits: int
    """ number of bits in the exponent """
    sig_bits: int
    """ number of bits in the significant """


@unique
class Builtin(Enum):
    BOOL = 'Bool'
    MEM = 'Mem'
    """ Memory """
    DOM = 'Dom'
    """ valid domain of memory operations """
    HTD = 'HTD'
    """ heap type description """
    PMS = 'PMS'
    """ phantom machine state """
    UNIT = 'UNIT'
    """ singleton type """
    TYPE = 'Type'
    """ type of Type expression used for pointer validity """
    TOKEN = 'Token'
    """ spec doesn't say what this is """
    ROUNDING_MODE = 'RoundingMode'


@dataclass(frozen=True, order=True)
class TypeBuiltin:
    builtin: Builtin


@dataclass(frozen=True, order=True)
class TypeWordArray:

    index_bits: int
    """ these are guesses from looking at the code, i don't actually know if
        that's what they're meant to represent

        number of bits used for the index?

        """

    value_bits: int
    """ number of bits used per value?
        same as for index_bits, i'm not actually sure
    """


Type = TypeStruct | TypeBitVec | TypePtr | TypeArray | TypeFloatingPoint | TypeBuiltin | TypeWordArray


def pretty_type_ascii(typ: Type) -> str:
    if isinstance(typ, TypeBitVec):
        return f'BitVec{typ.size}'
    elif isinstance(typ, TypeBuiltin):
        return typ.builtin.value
    elif isinstance(typ, TypeStruct):
        return str(typ)
    elif isinstance(typ, TypePtr):
        return str(typ)
    elif isinstance(typ, TypeArray):
        return str(typ)
    elif isinstance(typ, TypeFloatingPoint):
        return str(typ)
    elif isinstance(typ, TypeBuiltin):
        return str(typ)
    elif isinstance(typ, TypeWordArray):
        return str(typ)
    assert_never(typ)


type_bool: Type = TypeBuiltin(Builtin.BOOL)
type_word8 = TypeBitVec(8)
type_word32 = TypeBitVec(32)
type_word64 = TypeBitVec(64)


def convert_type(typ: syntax.Type) -> Type:
    if typ.kind == 'Word':
        if typ.num == 8:
            return type_word8
        elif typ.num == 32:
            return type_word32
        elif typ.num == 64:
            return type_word64
        return TypeBitVec(typ.num)
    elif typ.kind == 'Ptr':
        assert typ.el_typ_symb is not None
        return TypePtr(typ.el_typ_symb)
    elif typ.kind == 'Array':
        assert typ.el_typ_symb is not None
        return TypeArray(typ.el_typ_symb, typ.num)
    elif typ.kind == 'FloatingPoint':
        assert False, "floating points not supported yet"
        return TypeFloatingPoint(typ.nums[0], typ.nums[1])
    elif typ.kind == 'Struct':
        return TypeStruct(typ.name)
    elif typ.kind == 'Builtin':
        return TypeBuiltin(Builtin(typ.name))
    elif typ.kind == 'WordArray':
        return TypeWordArray(typ.nums[0], typ.nums[1])
    raise NotImplementedError(f"Type {typ.kind} not implemented")


@dataclass(frozen=True)
class ABCExpr(Generic[TypeKind, VarNameKind]):
    typ: TypeKind


@dataclass(frozen=True, order=True)
class ExprVar(ABCExpr[TypeKind, VarNameKind]):
    name: VarNameKind


ExprVarT: TypeAlias = ExprVar[Type, VarNameKind]


@dataclass(frozen=True)
class ExprNum(ABCExpr[TypeKind, Any]):
    num: int


ExprNumT: TypeAlias = ExprNum[Type]


@dataclass(frozen=True)
class ExprType(ABCExpr[TypeKind, Any]):
    """ should have typ builtin.Type
    """
    val: Type


ExprTypeT: TypeAlias = ExprType[Type]


@dataclass(frozen=True)
class ExprSymbol(ABCExpr[TypeKind, Any]):
    name: str


ExprSymbolT: TypeAlias = ExprSymbol[Type]

FunctionName = NewType('FunctionName', str)
""" This is an *smt* function, not a C function """


@dataclass(frozen=True)
class ExprFunction(ABCExpr[VarNameKind, TypeKind]):
    """ This is an *smt* function, not a C function """
    function_name: FunctionName
    arguments: Sequence[Expr[VarNameKind, TypeKind]]


ExprFunctionT: TypeAlias = ExprFunction[Type, VarNameKind]


@unique
class Operator(Enum):
    """ To convert graph lang operator name to this enum, just do Operator(parsed_operator_name)

    Some operators that are specified in the spec aren't used.
    Some operators that are used aren't specified in the spec.
    """
    PLUS = 'Plus'
    MINUS = 'Minus'
    TIMES = 'Times'
    MODULUS = 'Modulus'
    DIVIDED_BY = 'DividedBy'

    BW_AND = 'BWAnd'
    BW_OR = 'BWOr'
    BW_XOR = 'BWXor'

    SHIFT_LEFT = 'ShiftLeft'
    SHIFT_RIGHT = 'ShiftRight'
    SIGNED_SHIFT_RIGHT = 'SignedShiftRight'

    AND = 'And'
    OR = 'Or'
    IMPLIES = 'Implies'

    NOT = 'Not'

    TRUE = 'True'
    FALSE = 'False'

    EQUALS = 'Equals'
    LESS = 'Less'
    LESS_EQUALS = 'LessEquals'
    SIGNED_LESS = 'SignedLess'
    SIGNED_LESS_EQUALS = 'SignedLessEquals'

    BW_NOT = 'BWNot'
    WORD_REVERSE = 'WordReverse'
    WORD_CAST = 'WordCast'
    WORD_CAST_SIGNED = 'WordCastSigned'

    MEM_ACC = 'MemAcc'
    MEM_UPDATE = 'MemUpdate'

    WORD_ARRAY_ACCESS = 'WordArrayAccess'
    WORD_ARRAY_UPDATE = 'WordArrayUpdate'

    P_VALID = 'PValid'
    P_WEAK_VALID = 'PWeakValid'
    P_ALIGN_VALID = 'PAlignValid'
    P_GLOBAL_VALID = 'PGlobalValid'
    P_ARRAY_VALID = 'PArrayValid'

    MEM_DOM = 'MemDom'
    HTD_UPDATE = 'HTDUpdate'
    IF_THEN_ELSE = 'IfThenElse'

    # COUNT_LEADING_ZEROES = 'CountLeadingZeros'
    # COUNT_TRAILING_ZEROES = 'CountTrailingZeroes'

    # ROUND_NEAREST_TIES_TO_EVEN = 'roundNearestTiesToEven'
    # ROUND_NEAREST_TIES_TO_AWAY = 'roundNearestTiesToAway'
    # ROUND_TOWARD_POSITIVE = 'roundTowardPositive'
    # ROUND_TOWARD_NEGATIVE = 'roundTowardNegative'
    # ROUND_TOWARD_ZERO = 'roundTowardZero'

    # optional apparently
    # FP_ABS = 'fp.abs'
    # FP_NEG = 'fp.neg'
    # FP_ADD = 'fp.add'
    # FP_SUB = 'fp.sub'
    # FP_MUL = 'fp.mul'
    # FP_DIV = 'fp.div'
    # FP_FMA = 'fp.fma'
    # FP_SQRT = 'fp.sqrt'
    # FP_REM = 'fp.rem'
    # FP_ROUND_TO_INTEGRAL = 'fp.roundToIntegral'
    # FP_MIN = 'fp.min'
    # FP_MAX = 'fp.max'
    # FP_LEQ = 'fp.leq'
    # FP_LT = 'fp.lt'
    # FP_GEQ = 'fp.geq'
    # FP_GT = 'fp.gt'
    # FP_EQ = 'fp.eq'
    # FP_IS_NORMAL = 'fp.isNormal'
    # FP_IS_SUBNORMAL = 'fp.IsSubnormal'
    # FP_IS_ZERO = 'fp.isZero'
    # FP_IS_INFINITE = 'fp.isInfinite'
    # FP_IS_NAN = 'fp.isNaN'
    # FP_IS_NEGATIVE = 'fp.isNegative'
    # FP_IS_POSITIVE = 'fp.isPositive'

    # TO_FLOATING_POINT = 'ToFloatingPoint'
    # TO_FLOATING_POINT_SIGNED = 'ToFloatingPointSigned'
    # TO_FLOATING_POINT_UNSIGNED = 'ToFloatingPointUnsigned'
    # FLOATING_POINT_CAST = 'FloatingPointCast'


# operators that take no arguments
nulary_operators = {Operator.TRUE, Operator.FALSE}

pretty_binary_operators_ascii = {
    Operator.PLUS: '+',
    Operator.MINUS: '-',

    Operator.TIMES: '*',
    Operator.MODULUS: '%',
    Operator.DIVIDED_BY: '/',

    Operator.BW_AND: '&',
    Operator.BW_OR: '|',
    Operator.BW_XOR: '^',

    Operator.SHIFT_LEFT: '<<',
    Operator.SHIFT_RIGHT: '>>',
    Operator.SIGNED_SHIFT_RIGHT: '>>s',

    Operator.AND: '&&',
    Operator.OR: '||',
    Operator.IMPLIES: '->',

    Operator.EQUALS: '=',
    Operator.LESS: '<',
    Operator.LESS_EQUALS: '<=',
    Operator.SIGNED_LESS: '<s',
    Operator.SIGNED_LESS_EQUALS: '<=s',
}


@dataclass(frozen=True)
class ExprOp(ABCExpr[VarNameKind, TypeKind]):
    operator: Operator
    operands: tuple[Expr[VarNameKind, TypeKind], ...]


ExprOpT: TypeAlias = ExprOp[VarNameKind, Type]

Expr: TypeAlias = ExprVar[TypeKind, VarNameKind] | ExprNum[TypeKind] | ExprType[TypeKind] | ExprOp[TypeKind,
                                                                                                   VarNameKind] | ExprFunction[TypeKind, VarNameKind] | ExprSymbol[TypeKind]
ExprT: TypeAlias = Expr[Type, VarNameKind]

ProgVar: TypeAlias = ExprVarT[ProgVarName]

expr_true: Expr[Type, Any] = ExprOp(type_bool, Operator.TRUE, ())
expr_false: Expr[Type, Any] = ExprOp(type_bool, Operator.FALSE, ())

# testing the type checker
expr0: Expr[int, str] = ExprVar(2, 'variable')  # pass
expr1: Expr[Type, str] = ExprVar(type_bool, 'variable')  # pass
expr2: ExprT[str] = ExprVar(type_bool, 'variable')  # pass
expr3: ExprT[str] = ExprVar(type_bool, 'variable')  # pass
expr4: ExprVar[Type, str] = ExprVar(type_bool, 'foo')  # pass
expr5: ExprVarT[str] = ExprVar(type_bool, 'bar')  # pass
# expr5: Expr[int, bool] = ExprOp(type_bool, Operator.AND, ())  # fail


def visit_expr(expr: ExprT[VarNameKind], visitor: Callable[[ExprT[VarNameKind]], None]) -> None:
    visitor(expr)
    if isinstance(expr, ExprOp):
        for operand in expr.operands:
            visit_expr(operand, visitor)
    elif isinstance(expr, ExprFunction):
        for arg in expr.arguments:
            visit_expr(arg, visitor)
    elif not isinstance(expr, ExprVar | ExprNum | ExprType | ExprSymbol):
        assert_never(expr)


def expr_where_vars_are_used_in_node(node: Node[VarNameKind], selection: Set[ExprVarT[VarNameKind]]) -> Iterator[tuple[ExprVarT[VarNameKind], ExprT[VarNameKind]]]:
    if isinstance(node, NodeBasic):
        for upd in node.upds:
            for var in selection & all_vars_in_expr(upd.expr):
                yield var, upd.expr
    elif isinstance(node, NodeCall):
        for arg in node.args:
            for var in selection & all_vars_in_expr(arg):
                yield var, arg
    elif isinstance(node, NodeCond):
        for var in selection & all_vars_in_expr(node.expr):
            yield var, node.expr
    elif not isinstance(node, NodeEmpty):
        assert_never(node)


def pretty_expr_ascii(expr: ExprT[VarNameKind]) -> str:
    if isinstance(expr, ExprNum):
        return str(expr.num)
    elif isinstance(expr, ExprSymbol):
        return expr.name
    elif isinstance(expr, ExprType):
        return str(expr.val)
    elif isinstance(expr, ExprVar):
        if isinstance(expr.name, str):
            return expr.name
        if isinstance(expr.name, tuple):
            assert len(expr.name) == 2
            assert isinstance(expr.name[0], str)
            assert isinstance(expr.name[1], int)
            return f'{expr.name[0]}:{expr.name[1]}'
        assert False, f'{expr}'
    elif isinstance(expr, ExprOp):
        if expr.operator in pretty_binary_operators_ascii:
            assert len(expr.operands) == 2
            return f'({pretty_expr_ascii(expr.operands[0])} {pretty_binary_operators_ascii[expr.operator]} {pretty_expr_ascii(expr.operands[1])})'
        elif expr.operator == Operator.IF_THEN_ELSE:
            assert len(expr.operands) == 3
            cond, then, otherwise = (pretty_expr_ascii(operand)
                                     for operand in expr.operands)
            return f'({cond} ? {then} : {otherwise})'
        else:
            return f'{expr.operator.value}({", ".join(pretty_expr_ascii(operand) for operand in expr.operands)})'
    elif isinstance(expr, ExprFunction):
        return f'{expr.function_name} {" ".join(pretty_expr_ascii(arg) for arg in expr.arguments)}'
    assert_never(expr)


def convert_expr(expr: syntax.Expr) -> ExprT[ProgVarName]:
    typ = convert_type(expr.typ)
    if expr.kind == 'Op':
        return ExprOp(typ, Operator(expr.name), tuple(convert_expr(operand) for operand in expr.vals))
    elif expr.kind == 'Var':
        return ExprVar(typ, ProgVarName(expr.name))
    elif expr.kind == 'Num':
        return ExprNum(typ, expr.val)
    elif expr.kind == 'Type':
        return ExprType(typ, convert_type(expr.val))
    elif expr.kind == 'Symbol':
        return ExprSymbol(typ, expr.name)
    raise NotImplementedError


def all_vars_in_expr(expr: ExprT[VarNameKind]) -> set[ExprVarT[VarNameKind]]:
    s: set[ExprVarT[VarNameKind]] = set()

    def visitor(expr: ExprT[VarNameKind]) -> None:
        if isinstance(expr, ExprVar):
            s.add(ExprVar(expr.typ, expr.name))
    visit_expr(expr, visitor)
    return s


def expr_negate(expr: ExprT[VarNameKind]) -> ExprT[VarNameKind]:
    assert expr.typ == type_bool

    if isinstance(expr, ExprOp) and expr.operator == Operator.NOT:
        assert len(expr.operands) == 1
        return expr.operands[0]

    if expr == expr_true:
        return expr_false
    if expr == expr_false:
        return expr_true

    return ExprOp(type_bool, Operator.NOT, (expr, ))


def expr_or(lhs: ExprT[VarNameKind], rhs: ExprT[VarNameKind]) -> ExprT[VarNameKind]:
    assert lhs.typ == type_bool
    assert rhs.typ == type_bool

    if lhs == expr_true or rhs == expr_true:
        return expr_true
    if lhs == expr_false:
        return rhs
    if rhs == expr_false:
        return lhs

    return ExprOp(type_bool, Operator.OR, (lhs, rhs))


def expr_and(lhs: ExprT[VarNameKind], rhs: ExprT[VarNameKind]) -> ExprT[VarNameKind]:
    assert lhs.typ == type_bool
    assert rhs.typ == type_bool

    if lhs == expr_true:
        return rhs
    if rhs == expr_true:
        return lhs
    if lhs == expr_false or rhs == expr_false:
        return expr_false

    return ExprOp(type_bool, Operator.AND, (lhs, rhs))


def expr_implies(antecedent: ExprT[VarNameKind], consequent: ExprT[VarNameKind]) -> ExprT[VarNameKind]:
    assert antecedent.typ == type_bool
    assert consequent.typ == type_bool
    return ExprOp(type_bool, Operator.IMPLIES, (antecedent, consequent))


def expr_split_conjuncts(expr: ExprT[VarNameKind]) -> Iterator[ExprT[VarNameKind]]:
    if isinstance(expr, ExprOp) and expr.operator == Operator.AND:
        yield from expr_split_conjuncts(expr.operands[0])
        yield from expr_split_conjuncts(expr.operands[1])
    else:
        yield expr


def condition_to_evaluate_subexpr_in_expr(expr: ExprT[VarNameKind], sub: ExprT[VarNameKind]) -> ExprT[VarNameKind]:
    # traverse down the if, building up the condition to reach a particular variable
    if isinstance(expr, ExprNum):
        if expr == sub:
            return expr_true
        return expr_false
    elif isinstance(expr, ExprVar):
        if expr == sub:
            return expr_true
        return expr_false
    elif isinstance(expr, ExprOp):
        reachability_condition = [condition_to_evaluate_subexpr_in_expr(
            operand, sub) for operand in expr.operands]

        disjunctions = [d for d in reachability_condition if d != expr_false]

        # none of the operands use the sub expression
        if len(disjunctions) == 0:
            return expr_false

        if expr.operator is Operator.IF_THEN_ELSE and reachability_condition != [expr_true, expr_true]:
            assert len(expr.operands) == 3
            cond, then, otherwise = expr.operands

            # a bunch of shortcuts to emit smaller expressions
            # sub expression is used in the condition, so there is no escaping anything
            if reachability_condition[0] == expr_true:
                return expr_true
            if reachability_condition[0] == expr_false and reachability_condition[1] == expr_false:
                return expr_and(expr_negate(cond), reachability_condition[2])
            if reachability_condition[0] == expr_false and reachability_condition[2] == expr_false:
                return expr_and(cond, reachability_condition[1])

            # subexpr used in condition
            #   OR (condition AND subexpr used in then branch)
            #   OR (NOT condition AND subexpr used in else branch)

            branches = expr_or(
                expr_and(cond, reachability_condition[1]),
                expr_and(expr_negate(cond), reachability_condition[2])
            )
            return expr_or(reachability_condition[0], branches)

        # one operand always uses the sub expression
        if expr_true in disjunctions:
            return expr_true

        # either sub expression is used in first operand, or second operand, etc...
        cond = disjunctions[0]
        for op in disjunctions[1:]:
            cond = expr_or(cond, op)
        return cond
    elif isinstance(expr, ExprFunction):
        conditions = [condition_to_evaluate_subexpr_in_expr(
            arg, sub) for arg in expr.arguments]
        cond = expr_false
        for op in conditions:
            cond = expr_or(cond, op)
        return cond

    elif isinstance(expr, ExprType | ExprSymbol):
        assert False, "I'm not sure what this is suppose to mean"
    assert_never(expr)

# for the following commented out expr classes
# not present in the kernel functions, I don't want to make an abstraction for
# something i can't even test once

# @dataclass(frozen=True)
# class ExprField(ExprT[VarNameKind]):
#     struct: ExprT[VarNameKind]
#     field_name: str
#     field_type: Type

# @dataclass(frozen=True)
# class ExprFieldUpd(ExprT[VarNameKind]):
#     struct: ExprT[VarNameKind]
#     field_name: str
#     field_type: Type
#     val: ExprT[VarNameKind]

#
# @dataclass(frozen=True)
# class ExprStructCons(ExprT[VarNameKind]):
#     inits: Mapping[]


@dataclass(frozen=True)
class Update(Generic[VarNameKind]):
    var: ExprVar[Type, VarNameKind]
    expr: ExprT[VarNameKind]


@dataclass(frozen=True)
class NodeEmpty:
    succ: NodeName


@dataclass(frozen=True)
class NodeBasic(Generic[VarNameKind]):
    upds: tuple[Update[VarNameKind], ...]
    succ: NodeName


@dataclass(frozen=True)
class NodeCall(Generic[VarNameKind]):
    succ: NodeName
    fname: str
    args: tuple[ExprT[VarNameKind], ...]
    rets: tuple[ExprVar[Type, VarNameKind], ...]


@dataclass(frozen=True)
class NodeCond(Generic[VarNameKind]):
    expr: ExprT[VarNameKind]
    succ_then: NodeName
    succ_else: NodeName


Node = NodeBasic[VarNameKind] | NodeCall[VarNameKind] | NodeCond[VarNameKind] | NodeEmpty

LoopHeaderName = NewType('LoopHeaderName', NodeName)


@dataclass(frozen=True)
class Loop(Generic[VarNameKind]):
    back_edge: tuple[NodeName, NodeName]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[NodeName, ...]
    """ nodes forming a natural loop """

    targets: Sequence[ExprVarT[VarNameKind]]
    """ All the variables that are written to during the loop
    """

    @property
    def header(self) -> NodeName:
        return self.back_edge[1]


# FIXME: circular import
import abc_cfg  # nopep8


@dataclass(frozen=True)
class Function(Generic[VarNameKind]):

    name: str

    cfg: abc_cfg.CFG

    # TODO: find good way to freeze dict and keep type hints
    nodes: Mapping[NodeName, Node[VarNameKind]]
    """
    Node name => Node
    """

    loops: Mapping[LoopHeaderName, Loop[VarNameKind]]
    """
    loop header => loop information
    """

    arguments: tuple[ExprVarT[VarNameKind], ...]

    def is_loop_header(self, node_name: NodeName) -> LoopHeaderName | None:
        if node_name in self.loops:
            return LoopHeaderName(node_name)
        return None

    def is_loop_latch(self, node_name: NodeName) -> bool:
        """ A loop latch is a node which jumps back to the loop header """
        return any((node_name, succ) in self.cfg.back_edges for succ in self.cfg.all_succs[node_name])

    def acyclic_preds_of(self, node_name: NodeName) -> Iterator[NodeName]:
        """ returns all the direct predecessors, removing the ones that would follow back edges """
        return (p for p in self.cfg.all_preds[node_name] if (p, node_name) not in self.cfg.back_edges)

    def traverse_topologically_bottom_up(self: Function[VarNameKind]) -> Iterator[NodeName]:
        q: list[NodeName] = [n for n, succs in self.cfg.all_succs.items() if len(
            [succ for succ in succs if (n, succ) not in self.cfg.back_edges]) == 0]
        visited: set[NodeName] = set()

        while q:
            n = q.pop(-1)
            if n in visited:
                continue

            if any(succ not in visited for succ in self.cfg.all_succs[n] if (n, succ) not in self.cfg.back_edges):
                continue

            visited.add(n)
            yield n

            for pred in self.cfg.all_preds[n]:
                if (pred, n) not in self.cfg.back_edges:
                    q.append(pred)

        assert len(visited - {NodeNameErr, NodeNameRet}
                   ) == len(self.nodes), visited

    def traverse_topologically(self: Function[VarNameKind]) -> Iterator[NodeName]:
        q: list[NodeName] = [
            n for n, preds in self.cfg.all_preds.items() if len([p for p in self.acyclic_preds_of(n)]) == 0]
        visited: set[NodeName] = set()
        while q:
            n = q.pop(-1)
            if n in visited:
                continue

            if not all(p in visited for p in self.acyclic_preds_of(n)):
                continue

            visited.add(n)
            yield n

            for succ in self.cfg.all_succs[n]:
                if (n, succ) not in self.cfg.back_edges:
                    q.append(succ)

        assert len(visited - {NodeNameErr, NodeNameRet}) == len(self.nodes)


def used_variables_in_node(node: Node[VarNameKind]) -> Set[ExprVarT[VarNameKind]]:
    used_variables: set[ExprVarT[VarNameKind]] = set()
    if isinstance(node, NodeBasic):
        for upd in node.upds:
            used_variables |= all_vars_in_expr(upd.expr)
    elif isinstance(node, NodeCall):
        for arg in node.args:
            used_variables |= all_vars_in_expr(arg)
    elif isinstance(node, NodeCond):
        used_variables |= all_vars_in_expr(node.expr)
    elif not isinstance(node, NodeEmpty):
        assert_never(node)
    return used_variables


def assigned_variables_in_node(func: Function[VarNameKind], n: NodeName, *, with_loop_targets: bool) -> Set[ExprVarT[VarNameKind]]:
    if n in (NodeNameRet, NodeNameErr):
        return set()

    assigned_variables: set[ExprVarT[VarNameKind]] = set()
    node = func.nodes[n]
    if isinstance(node, NodeBasic):
        assigned_variables.update(upd.var for upd in node.upds)
    elif isinstance(node, NodeCall):
        assigned_variables.update(ret for ret in node.rets)
    elif not isinstance(node, NodeEmpty | NodeCond):
        assert_never(node)

    if (loop_header := func.is_loop_header(n)) and with_loop_targets:
        assigned_variables.update(func.loops[loop_header].targets)

    return assigned_variables


def convert_function_nodes(nodes: Mapping[str | int, syntax.Node]) -> Mapping[NodeName, Node[ProgVarName]]:
    safe_nodes: dict[NodeName, Node[ProgVarName]] = {}
    for name, node in nodes.items():
        name = NodeName(str(name))
        if node.kind == "Basic":
            if len(node.upds) == 0:
                safe_nodes[name] = NodeEmpty(succ=NodeName(str(node.cont)))
            else:
                upds: list[Update[ProgVarName]] = []
                for var, expr in node.upds:
                    upds.append(Update(
                        var=ExprVarT[ProgVarName](
                            convert_type(var[1]), ProgVarName(var[0])),
                        expr=convert_expr(expr)))
                safe_nodes[name] = NodeBasic(upds=tuple(
                    upds), succ=NodeName(str(node.cont)))
        elif node.kind == "Call":
            node.args
            safe_nodes[name] = NodeCall(
                succ=NodeName(str(node.cont)),
                fname=node.fname,
                args=tuple(convert_expr(arg) for arg in node.args),
                rets=tuple(ExprVar(convert_type(typ), ProgVarName(name)) for name, typ in node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = NodeCond(
                succ_then=NodeName(str(node.left)), succ_else=NodeName(str(node.right)), expr=convert_expr(node.cond))
        else:
            raise ValueError(f"unknown kind {node.kind!r}")
    return safe_nodes


def convert_function(func: syntax.Function) -> Function[ProgVarName]:
    safe_nodes = convert_function_nodes(func.nodes)
    all_succs = abc_cfg.compute_all_successors_from_nodes(safe_nodes)
    assert func.entry is not None
    cfg = abc_cfg.compute_cfg_from_all_succs(
        all_succs, NodeName(str(func.entry)))
    loops = abc_cfg.compute_loops(safe_nodes, cfg)

    args = tuple(ExprVar(convert_type(typ), ProgVarName(name))
                 for name, typ in func.inputs)

    return Function(cfg=cfg, nodes=safe_nodes, loops=loops, arguments=args, name=func.name)
