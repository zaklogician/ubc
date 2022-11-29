from __future__ import annotations
import dataclasses
from enum import Enum, unique
from typing import Callable, Generic, Mapping, NamedTuple, NewType, Reversible, TypeAlias, TypeVar, cast
import syntax
from collections.abc import Collection
from dataclasses import dataclass
from functools import reduce
from collections import namedtuple

from typing_extensions import assert_never

# TODO: convert lists to tuples


class CFG(NamedTuple):
    """
    Class that groups information about a function's control flow graph
    """

    entry: str
    # TODO: make those lists a tuple/Collection/Sequence/Set?
    all_succs: Mapping[str, list[str]]
    """ Successors """

    all_preds: Mapping[str, list[str]]
    """ Predecessors """

    all_doms: Mapping[str, list[str]]
    """ Dominators of key (a in all_doms[b] means a dominates b) """

    back_edges: Collection[tuple[str, str]]
    """ edges where the head dominates the tail
        Stored as (tail, head), that is (latch, loop_header)
    """


class EmptyNode(NamedTuple):
    succ: str


ProgVarName = NewType('ProgVarName', str)
DSAVarName = NewType('DSAVarName', str)


def make_dsa_var_name(v: ProgVarName, k: int) -> DSAVarName:
    return DSAVarName(f'{v}.{k}')


def unpack_dsa_var_name(v: DSAVarName) -> tuple[ProgVarName, int]:
    name, num = v.rsplit('.', maxsplit=1)
    return ProgVarName(name), int(num)


VarKind = TypeVar('VarKind', ProgVarName, DSAVarName)


@dataclass(frozen=True)
class Type:
    pass


@dataclass(frozen=True)
class TypeStruct(Type):
    name: str


@dataclass(frozen=True)
class TypeBitVec(Type):
    """ Synonym for TypeWord
    """
    size: int


@dataclass(frozen=True)
class TypeArray(Type):
    element_typ: Type
    size: int


@dataclass(frozen=True)
class TypePtr(Type):
    pointee_type: Type


@dataclass(frozen=True)
class TypeFloatingPoint(Type):
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


@dataclass(frozen=True)
class TypeBuiltin(Type):
    builtin: Builtin


@dataclass(frozen=True)
class TypeWordArray(Type):

    index_bits: int
    """ these are guesses from looking at the code, i don't actually know if
        that's what they're meant to represent

        number of bits used for the index?

        """

    value_bits: int
    """ number of bits used per value?
        same as for index_bits, i'm not actually sure
    """
    pass


@dataclass(frozen=True)
class ABCExpr(Generic[VarKind]):
    typ: Type


@dataclass(frozen=True)
class ExprArray(ABCExpr[VarKind]):
    values: tuple[Expr[VarKind], ...]


@dataclass(frozen=True)
class ExprVar(ABCExpr[VarKind]):
    name: VarKind


@dataclass(frozen=True)
class ExprNum(ABCExpr):
    num: int


@dataclass(frozen=True)
class ExprType(ABCExpr[VarKind]):
    """ should have typ builtin.Type
    """
    val: Type


@dataclass(frozen=True)
class ExprSymbol(ABCExpr):
    name: str


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
    COUNT_LEADING_ZEROES = 'CountLeadingZeros'
    COUNT_TRAILING_ZEROES = 'CountTrailingZeroes'
    WORD_REVERSE = 'WordReverse'
    WORD_CAST = 'WordCast'
    WORD_CAST_SIGNED = 'WordCastSigned'

    MEM_ACC = 'MemAcc'
    MEM_UPDATE = 'MemUpdate'

    P_VALID = 'PValid'
    P_WEAK_VALID = 'PWeakValid'
    P_ALIGN_VALID = 'PAlignValid'
    P_GLOBAL_VALID = 'PGlobalValid'
    P_ARRAY_VALID = 'PArrayValid'

    MEM_DOM = 'MemDom'
    HTD_UPDATE = 'HTDUpdate'
    IF_THEN_ELSE = 'IfThenElse'

    ROUND_NEAREST_TIES_TO_EVEN = 'roundNearestTiesToEven'
    ROUND_NEAREST_TIES_TO_AWAY = 'roundNearestTiesToAway'
    ROUND_TOWARD_POSITIVE = 'roundTowardPositive'
    ROUND_TOWARD_NEGATIVE = 'roundTowardNegative'
    ROUND_TOWARD_ZERO = 'roundTowardZero'

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


@dataclass(frozen=True)
class ExprOp(ABCExpr[VarKind]):
    operator: Operator
    operands: tuple[Expr[VarKind], ...]


Expr = ExprArray[VarKind] | ExprVar[VarKind] | ExprNum | ExprType[VarKind] | ExprOp[VarKind] | ExprSymbol

# for the following commented out expr classes
# not present in the kernel functions, I don't want to make an abstraction for
# something i can't even test once

# @dataclass(frozen=True)
# class ExprField(Expr[VarKind]):
#     struct: Expr[VarKind]
#     field_name: str
#     field_type: Type

# @dataclass(frozen=True)
# class ExprFieldUpd(Expr[VarKind]):
#     struct: Expr[VarKind]
#     field_name: str
#     field_type: Type
#     val: Expr[VarKind]

#
# @dataclass(frozen=True)
# class ExprStructCons(Expr[VarKind]):
#     inits: Mapping[]


# can't inherit from NamedTuple and Generic[...], the fix is only in
# python3.11 and ubuntu comes with python3.10.
# https://github.com/python/cpython/issues/88089
# https://github.com/python/cpython/pull/92027
@dataclass(frozen=True)
class Var(Generic[VarKind]):
    name: VarKind
    typ: Type


@dataclass(frozen=True)
class Update(Generic[VarKind]):
    var: Var[VarKind]
    expr: Expr[VarKind]


@dataclass(frozen=True)
class BasicNode(Generic[VarKind]):
    # only support one update per node
    upd: Update[VarKind]
    succ: str


@dataclass(frozen=True)
class CallNode(Generic[VarKind]):
    succ: str
    fname: str
    args: tuple[Expr[VarKind], ...]
    rets: tuple[Var[VarKind], ...]


@dataclass(frozen=True)
class CondNode(Generic[VarKind]):
    expr: Expr  # TODO: Expr will take a VarKind
    succ_then: str
    succ_else: str


Node = BasicNode[VarKind] | CallNode[VarKind] | CondNode[VarKind] | EmptyNode


@dataclass(frozen=True)
class Loop:
    back_edge: tuple[str, str]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[str, ...]
    """ nodes forming a natural loop """

    targets: Collection[ProgVarName]
    """ All the variables that are written to during the loop
    """

    @property
    def header(self):
        return self.back_edge[1]


@dataclass(frozen=True)
class Function(Generic[VarKind]):

    cfg: CFG

    name: str

    # TODO: find good way to freeze dict and keep type hints
    nodes: Mapping[str, Node[VarKind]]
    """
    Node name => Node
    """

    loops: Mapping[str, Loop]
    """
    loop header => loop information
    """

    arguments: tuple[Var[VarKind], ...]

    def is_loop_header(self, node_name: str) -> bool:
        return node_name in self.loops


def visit_expr(expr: Expr, visitor: Callable[[Expr], None]):
    visitor(expr)
    if isinstance(expr, ExprOp):
        for operator in expr.operands:
            visitor(operator)
    elif isinstance(expr, ExprArray):
        for value in expr.values:
            visitor(value)
    elif not isinstance(expr, ExprVar | ExprNum | ExprType | ExprSymbol):
        assert_never(expr)


def compute_all_successors_from_unsafe_function(function: syntax.Function) -> Mapping[str, list[str]]:
    all_succs: dict[str, list[str]] = {}
    for name, node in function.nodes.items():
        all_succs[name] = []
        for cont in node.get_conts():
            all_succs[name].append(cont)

    assert 'Err' not in all_succs
    all_succs['Err'] = []

    assert 'Ret' not in all_succs
    all_succs['Ret'] = []
    return all_succs


def compute_all_successors_from_nodes(nodes: Mapping[str, Node]) -> Mapping[str, list[str]]:
    all_succs: dict[str, list[str]] = {}
    for name, node in nodes.items():
        all_succs[name] = []
        if isinstance(node, BasicNode | CallNode | EmptyNode):
            all_succs[name].append(node.succ)
        elif isinstance(node, CondNode):
            all_succs[name].append(node.succ_then)
            all_succs[name].append(node.succ_else)
        else:
            assert_never(node)

    assert 'Err' not in all_succs
    all_succs['Err'] = []

    assert 'Ret' not in all_succs
    all_succs['Ret'] = []
    return all_succs


def compute_all_predecessors(all_succs: Mapping[str, list[str]]) -> Mapping[str, list[str]]:
    g: Mapping[str, list[str]] = {n: [] for n in all_succs}
    for n, succs in all_succs.items():
        for succ in succs:
            g[succ].append(n)
    return g

# algorithm from https://en.wikipedia.org/wiki/Dominator_(graph_theory) there
# exists more efficient algorithms, but we can implement them if it turns out
# this is a bottle neck


def compute_dominators(all_succs: Mapping[str, list[str]], all_preds: Mapping[str, list[str]], entry: str) -> Mapping[str, list[str]]:
    # all the nodes that dominate the given node
    doms: dict[str, set[str]] = {}
    for n, preds in all_preds.items():
        if len(preds) == 0:
            doms[n] = set([n])
        else:
            doms[n] = set(all_preds.keys())

    changed = True
    while changed:
        changed = False

        for n in all_succs.keys():
            npreds = list(all_preds[n])
            if not npreds:
                continue

            new_dom = set([n]) | reduce(set.intersection,  # type: ignore [arg-type]
                                        (doms[p] for p in npreds), doms[npreds[0]])
            if new_dom != doms[n]:
                changed = True
                doms[n] = new_dom

    return {n: list(doms[n]) for n in doms.keys()}


def compute_cfg_from_all_succs(all_succs: Mapping[str, list[str]], entry: str):
    assert_valid_all_succs(all_succs)
    assert entry in all_succs, f"entry {entry} not in all_succs"

    all_preds = compute_all_predecessors(all_succs)
    assert len(all_preds) == len(all_succs)
    # assert is_valid_all_preds(all_preds)

    all_doms = compute_dominators(
        all_succs=all_succs, all_preds=all_preds, entry=entry)
    return CFG(entry=entry, all_succs=all_succs, all_preds=all_preds, all_doms=all_doms, back_edges=cfg_compute_back_edges(all_succs, all_doms))


def compute_cfg_from_func(func: syntax.Function) -> CFG:
    all_succs = compute_all_successors_from_unsafe_function(func)
    assert func.entry is not None, f"func.entry is None in {func.name}"
    return compute_cfg_from_all_succs(all_succs, func.entry)


def cfg_compute_back_edges(all_succs: Mapping[str, list[str]], all_doms: Mapping[str, list[str]]) -> Collection[tuple[str, str]]:
    """ a back edge is an edge who's head dominates their tail
    """

    back_edges: set[tuple[str, str]] = set()
    for n, succs in all_succs.items():
        tail = n
        for head in succs:
            if head in all_doms[tail]:
                back_edges.add((tail, head))
    return frozenset(back_edges)


def compute_natural_loop(cfg: CFG, back_edge: tuple[str, str]) -> tuple[str, ...]:
    """ Returns all the nodes in the loop

    The loop header uniquely identifies the loop unless we have multiple back
    edges pointing to the same node (right now, we bail out of this case)
    """
    n, d = back_edge
    assert d in cfg.all_doms[n]

    loop_nodes = set([d])
    stack = []

    def insert(m):
        if m not in loop_nodes:
            loop_nodes.add(m)
            stack.append(m)

    insert(n)
    while stack:
        m = stack.pop(-1)
        for p in cfg.all_preds[m]:
            insert(p)
    return tuple(loop_nodes)


def compute_loop_targets(
        nodes: Mapping[str, Node[VarKind]],
        cfg: CFG,
        loop_header: str,
        loop_nodes: tuple[str, ...]) -> Collection[VarKind]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[str] = [loop_header]
    visited = set()

    loop_targets: set[VarKind] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, BasicNode):
            loop_targets.add(node.upd.var.name)
        elif isinstance(node, CallNode):
            for ret in node.rets:
                loop_targets.add(ret.name)
        elif not isinstance(node, EmptyNode | CondNode):
            assert_never(node)

        for succ in cfg.all_succs[n]:
            if succ in loop_nodes and (n, succ) not in cfg.back_edges:
                q.append(succ)

    assert len(visited) == len(loop_nodes)
    return loop_targets


def assert_single_loop_header_per_loop(cfg: CFG):
    # This assert protects against this:
    #
    #   -> header <--
    #  /   /     \    \
    # |   /       \    |
    #  \  v        v  /
    #   left       right
    assert len(set(loop_header for (t, loop_header) in cfg.back_edges)) == len(cfg.back_edges), \
        "unhandle case: multiple back edges point to the same loop header in function"


def compute_loops(nodes: Mapping[str, Node[ProgVarName]], cfg: CFG) -> Mapping[str, Loop]:
    """ Map from loop header to Loop
    """
    assert_single_loop_header_per_loop(cfg)

    loops: dict[str, Loop] = {}
    # we could do this faster by traversing the entire graph once and keeping
    # track of which loop we are currently in, but this is approach simpler
    # and good enough for now
    for back_edge in cfg.back_edges:
        _, loop_header = back_edge

        loop_nodes = compute_natural_loop(cfg, back_edge)

        assert all(loop_header in cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        loop_targets = compute_loop_targets(
            nodes, cfg, loop_header, loop_nodes)
        loops[loop_header] = Loop(back_edge, loop_nodes, loop_targets)
    return loops


def convert_type(typ: syntax.Type) -> Type:
    if typ.kind == 'Word':
        return TypeBitVec(typ.num)
    elif typ.kind == 'Ptr':
        assert typ.el_typ_symb is not None
        return TypePtr(typ.el_typ_symb)
    elif typ.kind == 'Array':
        assert typ.el_typ_symb is not None
        return TypeArray(typ.el_typ_symb, typ.num)
    elif typ.kind == 'FloatingPoint':
        return TypeFloatingPoint(typ.nums[0], typ.nums[1])
    elif typ.kind == 'Struct':
        return TypeStruct(typ.name)
    elif typ.kind == 'Builtin':
        return TypeBuiltin(Builtin(typ.name))
    elif typ.kind == 'WordArray':
        return TypeWordArray(typ.nums[0], typ.nums[1])
    raise NotImplementedError(f"Type {typ.kind} not implemented")


def convert_expr(expr: syntax.Expr) -> Expr[ProgVarName]:
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


def _convert_function(func: syntax.Function) -> Function:
    cfg = compute_cfg_from_func(func)
    safe_nodes: dict[str, Node[ProgVarName]] = {}
    for name, node in func.nodes.items():
        if node.kind == "Basic":
            if len(node.upds) == 0:
                safe_nodes[name] = EmptyNode(succ=node.cont)
            else:
                assert len(
                    node.upds) == 1, "multiple simultaneous updates isn't supported yet"
                var = Var(ProgVarName(node.upds[0][0][0]), convert_type(
                    node.upds[0][0][1]))
                upd = Update(var=var, expr=convert_expr(node.upds[0][1]))
                safe_nodes[name] = BasicNode(upd=upd, succ=node.cont)
        elif node.kind == "Call":
            node.args
            safe_nodes[name] = CallNode(
                succ=node.cont,
                fname=node.fname,
                args=tuple(convert_expr(arg) for arg in node.args),
                rets=tuple(Var(ProgVarName(name), convert_type(typ)) for name, typ in node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = CondNode(
                succ_then=node.left, succ_else=node.right, expr=convert_expr(node.cond))
        else:
            raise ValueError(f"unknown kind {node.kind!r}")

    loops = compute_loops(safe_nodes, cfg)

    args = tuple(Var(ProgVarName(name), convert_type(typ))
                 for name, typ in func.inputs)

    return Function(cfg=cfg, nodes=safe_nodes, loops=loops, arguments=args, name=func.name)


def convert_function(func: syntax.Function) -> Function[ProgVarName]:
    try:
        f = _convert_function(func)
    except Exception as e:
        raise type(e)(f"in function {func.name!r}") from e
    return f


def num_reachable(cfg: CFG) -> int:
    q: list[str] = [n for n, preds in cfg.all_preds.items() if len(preds) == 0]
    visited = set()
    while q:
        n = q.pop(0)
        visited.add(n)
        if n not in cfg.all_succs:
            continue
        for cont in cfg.all_succs[n]:
            if cont not in visited:
                q.append(cont)
    return len(visited)


def cfg_is_reducible(cfg: CFG):
    # use definition of reducibility from Aho, Sethi and Ullman 1986 p.606
    #
    # 1. the forward edges form an acyclic graph in which every node can be
    #    reach from the entry
    # 2. the back edges consists only of edges whose head dominates their tail
    #    (tail --> head)

    visited = set()
    q: list[str] = [n for n, preds in cfg.all_preds.items() if len(preds) == 0]
    while q:
        n = q.pop(0)
        if n in visited:
            continue

        # Visit in topological order, that is, visit all the predecessors first.
        if all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges):
            visited.add(n)
            q += cfg.all_succs[n]
    # have we visited all the nodes? Not possible if there's a cycle, because
    # there would always be a predecessor who hadn't been visited yet
    return len(visited) == num_reachable(cfg)


def assert_valid_all_succs(all_succs: Mapping[str, list[str]]):
    # entry node should be a key of all_succs, even if they don't have any
    # successors
    for n, succs in all_succs.items():
        for succ in succs:
            assert succ in all_succs


class Insertion(NamedTuple):
    """ At joint nodes, we need to insert x_n = x_m
    These insertion items keep track of that.
    """

    after: str
    """ Will insert the update after the node 'after' """

    lhs_dsa_name: DSAVarName
    typ: Type

    rhs_dsa_value: DSAVarName


@dataclass
class DSABuilder:
    k: int
    """ Fresh incarnation count

    To allocate a new variable:

        s.k += 1
        make_dsa_var_name(base_name, s.k)

    Mutable during construction
    """

    insertions: list[Insertion]
    """ Nodes to insert (join nodes)

    Mutable during construction
    """

    loop_targets_incarnations: Mapping[str, dict[ProgVarName, DSAVarName]]
    """
    Loop header => prog_var_name => dsa_var_name

    (Recall that a loop header uniquely identifies a loop)

    When we read a variable from a block, we go up the CFG to find where it
    was defined. If we stumble upon a loop header, and this loop writes to
    that specific variable (ie this variable is a loop target), then we must
    not continue looking up the graph! That variable must be havoced.

    That is, the first time you lookup a loop target in the loop header, you
    return a fresh variable f. Later on, if more blocks ask for that same
    variable, we must return the same f.

    This mapping keeps track of which loop targets have been incarnated so far.

    Mutable during construction
    """

    func_args: tuple[Var[DSAVarName], ...]
    """ The function's arguments in with DSA numbers associated to the
        arguments

        Not mutated during construction
    """


def find_latest_incarnation(
        func: Function[ProgVarName],
        dsa_nodes: Mapping[str, Node[DSAVarName]],
        s: DSABuilder,
        current_node: str,
        target_var: ProgVarName,
        typ: Type,
        skip_current_node=False) -> DSAVarName:

    # see loop_targets_incarnations' comment
    if current_node in func.loops and target_var in func.loops[current_node].targets:

        if target_var not in s.loop_targets_incarnations[current_node]:
            s.k += 1
            s.loop_targets_incarnations[current_node][target_var] = make_dsa_var_name(
                target_var, s.k)

        return s.loop_targets_incarnations[current_node][target_var]

    # i think skip_current_node == current_node in dsa_nodes, but i'd just like to make sure
    if not skip_current_node:
        assert current_node in dsa_nodes, f"didn't traverse in topological order {current_node=}"

        node = dsa_nodes[current_node]
        if isinstance(node, BasicNode):
            name, _ = unpack_dsa_var_name(node.upd.var.name)
            if target_var == name:
                return node.upd.var.name
        elif isinstance(node, CallNode):
            for ret in node.rets:
                name, _ = unpack_dsa_var_name(ret.name)
                if name == target_var:
                    return ret.name
        elif not isinstance(node, EmptyNode | CondNode):
            assert_never(node)

        # otherwise, keep looking up the graph

    # don't go searching up back edges
    preds = [p for p in func.cfg.all_preds[current_node]
             if (p, current_node) not in func.cfg.back_edges]

    if len(preds) == 0:
        # is the variable an argument to the function?
        for arg in s.func_args:
            name, num = unpack_dsa_var_name(arg.name)
            if name == target_var:
                return arg.name

        # maybe it's a global
        # TODO
        assert False, f"trying to read {target_var} but reached top of the function (is it a global?)"

    if len(preds) == 1:
        return find_latest_incarnation(func, dsa_nodes, s, preds[0], target_var, typ)

    latest = [find_latest_incarnation(
        func, dsa_nodes, s, p, target_var, typ) for p in preds]

    if len(set(latest)) == 1:
        return latest[0]

    # different branch have given different variables
    # TODO: use Leino's optimisation to avoid excessive variables
    s.k = s.k + 1
    fresh_name = DSAVarName(target_var + f'.{s.k}')
    for i, pred in enumerate(preds):
        s.insertions.append(
            Insertion(after=pred, lhs_dsa_name=fresh_name,
                      typ=typ, rhs_dsa_value=latest[i])
        )

    return fresh_name


def apply_incarnations(
        func: Function[ProgVarName],
        graph: Mapping[str, Node],
        s: DSABuilder,
        current_node: str,
        root: Expr[ProgVarName]) -> Expr[DSAVarName]:

    # using the Expr.visit is annoying because I need to keep track of state
    # to rebuild the expression
    if isinstance(root, ExprNum):
        return root
    elif isinstance(root, ExprVar):
        dsa_name = find_latest_incarnation(
            func, graph, s, current_node, root.name, root.typ, skip_current_node=True)
        return ExprVar(root.typ, name=dsa_name)
    elif isinstance(root, ExprOp):
        return ExprOp(root.typ, Operator(root.operator), operands=tuple(
            apply_incarnations(func, graph, s, current_node, operand) for operand in root.operands
        ))
    elif isinstance(root, ExprArray | ExprType | ExprSymbol):
        raise NotImplementedError
    else:
        assert_never(root)

    raise NotImplementedError(f"expr={root}")


def apply_insertions(graph: dict[str, Node[DSAVarName]], insertions: Collection[Insertion]):
    for i, ins in enumerate(insertions):
        assert ins.after in graph, "inserting after an unknown node"
        after = graph[ins.after]
        # if we have a BasicNode, we could technically add an update.
        # However, I don't do this because (1) if the last node is a CallNode,
        # i'll have to insert an extra BasicNode anyway (2) c parser doesn't generate
        # basic nodes with more than one update anyway, so code handling multiple
        # updates either doesn't exists and isn't well tested

        # or we could find the latest basic node before the 'after' node
        # (we are guaranteed to find on the branch because otherwise we would
        # not have had a conflict to resolve in the first place)

        # approach: insert a basic node
        assert not isinstance(
            after, CondNode), "i didn't think this was possible"

        var = Var(DSAVarName(ins.lhs_dsa_name), ins.typ)
        expr = ExprVar(ins.typ, ins.rhs_dsa_value)
        joiner = BasicNode(Update(var, expr), succ=after.succ)
        joiner_name = f'j{i}'
        graph[joiner_name] = joiner

        # not type safe according to pyright!
        graph[ins.after] = dataclasses.replace(after, succ=joiner_name)


def recompute_loops_post_dsa(pre_dsa_loops: Mapping[str, Loop], dsa_nodes: Mapping[str, Node[DSAVarName]], cfg: CFG) -> Mapping[str, Loop]:
    """ Update the loop nodes (because dsa inserts some joiner nodes)
        but keep everything else the same (in particular the loop targets are still ProgVarName!)
    """
    assert_single_loop_header_per_loop(cfg)

    # loop header => loop nodes
    all_loop_nodes: dict[str, tuple[str, ...]] = {}
    for back_edge in cfg.back_edges:
        _, loop_header = back_edge
        loop_nodes = compute_natural_loop(cfg, back_edge)

        assert all(loop_header in cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        all_loop_nodes[loop_header] = loop_nodes

    assert all_loop_nodes.keys() == pre_dsa_loops.keys(
    ), "loop headers should remain the same through DSA transformation"

    loops: dict[str, Loop] = {}
    for loop_header, loop_nodes in all_loop_nodes.items():
        assert set(pre_dsa_loops[loop_header].nodes).issubset(
            loop_nodes), "dsa only inserts joiner nodes, all previous loop nodes should still be loop nodes"
        loops[loop_header] = Loop(back_edge=pre_dsa_loops[loop_header].back_edge,
                                  targets=pre_dsa_loops[loop_header].targets,
                                  nodes=loop_nodes)
    return loops


def dsa(func: Function[ProgVarName]) -> Function[DSAVarName]:
    # q = [n for n, preds in func.cfg.all_preds.items() if len(preds) == 0]
    q = [func.cfg.entry]

    dsa_nodes: dict[str, Node[DSAVarName]] = {}
    visited: set[str] = set()

    # this is hack to deal with the weird assert False() node
    for n, preds in func.cfg.all_preds.items():
        if len(preds) == 0 and n != func.cfg.entry:
            # assert len(expr_variables(func.nodes[n])) == 0  # TODO
            node = func.nodes[n]
            assert isinstance(node, CondNode) and node.expr == ExprOp(
                TypeBuiltin(Builtin.BOOL), Operator.FALSE, tuple()), "different weird case in c parser"
            dsa_nodes[n] = cast(CondNode[DSAVarName], node)
            visited.add(n)
            # if we can reach this annoying assert False, that means we must
            # be able to reach Err.
            visited.add('Err')

    k = 0
    dsa_args: list[Var[DSAVarName]] = []
    for arg in func.arguments:
        k += 1
        dsa_args.append(Var(make_dsa_var_name(arg.name, k), arg.typ))

    s = DSABuilder(k=k, insertions=[], loop_targets_incarnations={
                   loop_header: {} for loop_header in func.loops},
                   func_args=tuple(dsa_args))

    while q:
        # bfs-like topological order so that we visit the longest branches last
        n = q.pop(-1)
        if n == 'Err' or n == 'Ret':
            visited.add(n)
            continue

        # visit in topolocial order ignoring back edges
        if not all(p in visited for p in func.cfg.all_preds[n] if (p, n) not in func.cfg.back_edges):
            continue

        visited.add(n)

        node = func.nodes[n]
        if isinstance(node, BasicNode):
            s.k += 1
            varp = Var(make_dsa_var_name(
                node.upd.var.name, s.k), node.upd.var.typ)
            exprp = apply_incarnations(func, dsa_nodes, s, n, node.upd.expr)
            dsa_nodes[n] = BasicNode(Update(varp, exprp), succ=node.succ)
        elif isinstance(node, CondNode):
            dsa_nodes[n] = CondNode(
                expr=apply_incarnations(func, dsa_nodes, s, n, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, CallNode):
            rets: list[Var[DSAVarName]] = []
            for ret in node.rets:
                s.k += 1
                rets.append(Var(make_dsa_var_name(ret.name, s.k), ret.typ))
            dsa_nodes[n] = CallNode(
                succ=node.succ,
                args=tuple(apply_incarnations(func, dsa_nodes, s, n, arg)
                           for arg in node.args),
                rets=tuple(rets),
                fname=node.fname,
            )
        elif isinstance(node, EmptyNode):
            dsa_nodes[n] = node
        else:
            assert assert_never(node)

        succs = func.cfg.all_succs[n]
        for succ in succs:
            if (n, succ) not in func.cfg.back_edges:
                q.append(succ)

    apply_insertions(dsa_nodes, s.insertions)

    assert len(visited) == num_reachable(
        func.cfg), f"{visited} {len(visited)} {num_reachable(func.cfg)} {func.name}"

    # need to recompute the cfg
    all_succs = compute_all_successors_from_nodes(dsa_nodes)
    cfg = compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = recompute_loops_post_dsa(func.loops, dsa_nodes, cfg)

    return Function[DSAVarName](
        cfg=cfg,
        arguments=tuple(dsa_args),
        loops=loops,
        name=func.name,
        nodes=dsa_nodes)
