from __future__ import annotations
import dataclasses
from enum import Enum, unique
from os import curdir
from typing import Callable, Generic, Iterable, Iterator, Mapping, NamedTuple, NewType, Reversible, Set, TypeAlias, TypeVar, cast
from logic import entry_aligned_address
import syntax
from collections.abc import Collection
from dataclasses import dataclass
from functools import reduce
from collections import namedtuple

from typing_extensions import assert_never

# TODO: convert lists to tuples


NodeName = NewType('NodeName', str)
IncarnationNum = NewType('IncarnationNum', int)
IncarnationBase = IncarnationNum(1)

NodeNameErr = NodeName('Err')
NodeNameRet = NodeName('Ret')


class CFG(NamedTuple):
    """
    Class that groups information about a function's control flow graph
    """

    entry: NodeName
    # TODO: make those lists a tuple/Collection/Sequence/Set?
    all_succs: Mapping[NodeName, list[NodeName]]
    """ Successors """

    all_preds: Mapping[NodeName, list[NodeName]]
    """ Predecessors """

    all_doms: Mapping[NodeName, list[NodeName]]
    """ Dominators of key (a in all_doms[b] means a dominates b) """

    back_edges: Collection[tuple[NodeName, NodeName]]
    """ edges where the head dominates the tail
        Stored as (tail, head), that is (latch, loop_header)
    """


@dataclass(frozen=True)
class EmptyNode:
    succ: NodeName


ProgVarName = NewType('ProgVarName', str)
DSAVarName = NewType('DSAVarName', tuple[ProgVarName, IncarnationNum])
VarKind = TypeVar('VarKind', ProgVarName, DSAVarName)

# can't inherit from NamedTuple and Generic[...], the fix is only in
# python3.11 and ubuntu comes with python3.10.
# https://github.com/python/cpython/issues/88089
# https://github.com/python/cpython/pull/92027


@dataclass(frozen=True)
class Var(Generic[VarKind]):
    name: VarKind
    typ: Type


ProgVar = Var[ProgVarName]
DSAVar = Var[DSAVarName]


def make_dsa_var_name(v: ProgVarName, k: IncarnationNum) -> DSAVarName:
    return DSAVarName((v, k))


def unpack_dsa_var_name(v: DSAVarName) -> tuple[ProgVarName, IncarnationNum]:
    return v[0], v[1]


def unpack_dsa_var(var: DSAVar) -> tuple[ProgVar, IncarnationNum]:
    name, inc = unpack_dsa_var_name(var.name)
    return Var(name, var.typ), inc


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
class ExprVar(ABCExpr[VarKind]):
    name: VarKind


@dataclass(frozen=True)
class ExprNum(ABCExpr):
    num: int


@dataclass(frozen=True)
class ExprType(ABCExpr):
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


Expr = ExprVar[VarKind] | ExprNum | ExprType | ExprOp[VarKind] | ExprSymbol

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


@dataclass(frozen=True)
class Update(Generic[VarKind]):
    var: Var[VarKind]
    expr: Expr[VarKind]


@dataclass(frozen=True)
class BasicNode(Generic[VarKind]):
    upds: tuple[Update[VarKind], ...]
    succ: NodeName


@dataclass(frozen=True)
class CallNode(Generic[VarKind]):
    succ: NodeName
    fname: str
    args: tuple[Expr[VarKind], ...]
    rets: tuple[Var[VarKind], ...]


@dataclass(frozen=True)
class CondNode(Generic[VarKind]):
    expr: Expr  # TODO: Expr will take a VarKind
    succ_then: NodeName
    succ_else: NodeName


Node = BasicNode[VarKind] | CallNode[VarKind] | CondNode[VarKind] | EmptyNode


LoopHeaderName = NewType('LoopHeaderName', NodeName)


@dataclass(frozen=True)
class Loop(Generic[VarKind]):
    back_edge: tuple[NodeName, NodeName]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[NodeName, ...]
    """ nodes forming a natural loop """

    targets: Collection[Var[VarKind]]
    """ All the variables that are written to during the loop
    """

    @property
    def header(self) -> NodeName:
        return self.back_edge[1]


@dataclass(frozen=True)
class Function(Generic[VarKind]):

    name: str

    cfg: CFG

    # TODO: find good way to freeze dict and keep type hints
    nodes: Mapping[NodeName, Node[VarKind]]
    """
    Node name => Node
    """

    loops: Mapping[LoopHeaderName, Loop[VarKind]]
    """
    loop header => loop information
    """

    arguments: tuple[Var[VarKind], ...]

    def is_loop_header(self, node_name: NodeName) -> LoopHeaderName | None:
        if node_name in self.loops:
            return LoopHeaderName(node_name)

    def acyclic_preds_of(self, node_name: NodeName) -> tuple[NodeName, ...]:
        """ returns all the direct predecessors, removing the ones that would follow back edges """
        return tuple(p for p in self.cfg.all_preds[node_name] if (p, node_name) not in self.cfg.back_edges)


def visit_expr(expr: Expr, visitor: Callable[[Expr], None]):
    visitor(expr)
    if isinstance(expr, ExprOp):
        for operator in expr.operands:
            visitor(operator)
    elif not isinstance(expr, ExprVar | ExprNum | ExprType | ExprSymbol):
        assert_never(expr)


def compute_all_successors_from_nodes(nodes: Mapping[NodeName, Node]) -> Mapping[NodeName, list[NodeName]]:
    all_succs: dict[NodeName, list[NodeName]] = {}
    for name, node in nodes.items():
        all_succs[name] = []
        if isinstance(node, BasicNode | CallNode | EmptyNode):
            all_succs[name].append(node.succ)
        elif isinstance(node, CondNode):
            all_succs[name].append(node.succ_then)
            all_succs[name].append(node.succ_else)
        else:
            assert_never(node)

    # if there is at least one node jumping to Err (ie. at least one assert)
    # we add it
    for succs in all_succs.values():
        if NodeNameErr in succs:
            assert NodeNameErr not in all_succs
            all_succs[NodeNameErr] = []
            break

    assert any(NodeNameRet in succs for succs in all_succs.values()
               ), "I assumed at least one node should jump to NodeNameRet"

    assert NodeNameRet not in all_succs
    all_succs[NodeNameRet] = []

    return all_succs


def compute_all_predecessors(all_succs: Mapping[NodeName, list[NodeName]]) -> Mapping[NodeName, list[NodeName]]:
    g: Mapping[NodeName, list[NodeName]] = {n: [] for n in all_succs}
    for n, succs in all_succs.items():
        for succ in succs:
            g[succ].append(n)
    return g

# algorithm from https://en.wikipedia.org/wiki/Dominator_(graph_theory) there
# exists more efficient algorithms, but we can implement them if it turns out
# this is a bottle neck


def compute_dominators(all_succs: Mapping[NodeName, list[NodeName]], all_preds: Mapping[NodeName, list[NodeName]], entry: NodeName) -> Mapping[NodeName, list[NodeName]]:
    # all the nodes that dominate the given node
    doms: dict[NodeName, set[NodeName]] = {}
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


def compute_cfg_from_all_succs(all_succs: Mapping[NodeName, list[NodeName]], entry: NodeName):
    assert_valid_all_succs(all_succs)
    assert entry in all_succs, f"entry {entry} not in all_succs"

    all_preds = compute_all_predecessors(all_succs)
    assert len(all_preds) == len(all_succs)
    # assert is_valid_all_preds(all_preds)

    all_doms = compute_dominators(
        all_succs=all_succs, all_preds=all_preds, entry=entry)
    return CFG(entry=entry, all_succs=all_succs, all_preds=all_preds, all_doms=all_doms, back_edges=cfg_compute_back_edges(all_succs, all_doms))


def cfg_compute_back_edges(all_succs: Mapping[NodeName, list[NodeName]], all_doms: Mapping[NodeName, list[NodeName]]) -> Collection[tuple[NodeName, NodeName]]:
    """ a back edge is an edge who's head dominates their tail
    """

    back_edges: set[tuple[NodeName, NodeName]] = set()
    for n, succs in all_succs.items():
        tail = n
        for head in succs:
            if head in all_doms[tail]:
                back_edges.add((tail, head))
    return frozenset(back_edges)


def compute_natural_loop(cfg: CFG, back_edge: tuple[NodeName, NodeName]) -> tuple[NodeName, ...]:
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
        nodes: Mapping[NodeName, Node[VarKind]],
        cfg: CFG,
        loop_header: NodeName,
        loop_nodes: tuple[NodeName, ...]) -> Collection[Var[VarKind]]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[NodeName] = [loop_header]
    visited = set()

    loop_targets: set[Var[VarKind]] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, BasicNode):
            for upd in node.upds:
                loop_targets.add(upd.var)
        elif isinstance(node, CallNode):
            for ret in node.rets:
                loop_targets.add(ret)
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


def compute_loops(nodes: Mapping[NodeName, Node[ProgVarName]], cfg: CFG) -> Mapping[LoopHeaderName, Loop[ProgVarName]]:
    """ Map from loop header to Loop
    """
    assert_single_loop_header_per_loop(cfg)

    loops: dict[LoopHeaderName, Loop[ProgVarName]] = {}
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
        loops[LoopHeaderName(loop_header)] = Loop(
            back_edge, loop_nodes, loop_targets)
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


def convert_var(v: tuple[str, syntax.Type]) -> Var:
    return Var(ProgVarName(v[0]), convert_type(v[1]))


def _convert_function(func: syntax.Function) -> Function:
    safe_nodes: dict[NodeName, Node[ProgVarName]] = {}
    for name, node in func.nodes.items():
        name = NodeName(str(name))
        if node.kind == "Basic":
            if len(node.upds) == 0:
                safe_nodes[name] = EmptyNode(succ=NodeName(str(node.cont)))
            else:
                upds: list[Update] = []
                for var, expr in node.upds:
                    upds.append(Update(
                        var=convert_var(var),
                        expr=convert_expr(expr)))
                safe_nodes[name] = BasicNode(upds=tuple(
                    upds), succ=NodeName(str(node.cont)))
        elif node.kind == "Call":
            node.args
            safe_nodes[name] = CallNode(
                succ=NodeName(str(node.cont)),
                fname=node.fname,
                args=tuple(convert_expr(arg) for arg in node.args),
                rets=tuple(Var(ProgVarName(name), convert_type(typ)) for name, typ in node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = CondNode(
                succ_then=NodeName(str(node.left)), succ_else=NodeName(str(node.right)), expr=convert_expr(node.cond))
        else:
            raise ValueError(f"unknown kind {node.kind!r}")

    all_succs = compute_all_successors_from_nodes(safe_nodes)
    assert func.entry is not None
    cfg = compute_cfg_from_all_succs(all_succs, NodeName(str(func.entry)))
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
    q: list[NodeName] = [n for n, preds in cfg.all_preds.items()
                         if len(preds) == 0]
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
    q: list[NodeName] = [n for n, preds in cfg.all_preds.items()
                         if len(preds) == 0]
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


def assert_valid_all_succs(all_succs: Mapping[NodeName, list[NodeName]]):
    # entry node should be a key of all_succs, even if they don't have any
    # successors
    for n, succs in all_succs.items():
        for succ in succs:
            assert succ in all_succs, f"{succ=} {all_succs.keys()=}"


class Insertion(NamedTuple):
    """ At joint nodes, we need to insert x_n = x_m
    These insertion items keep track of that.
    """


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


# if cond
#     a = 2
# else:
#     a = 3
#     a = a + 1
# a = a + 1

# if cond1  {cond: {1}}
#     {cond: {1}}
#     a1 = 2  {cond: {1}, a: {1}}
#     ; a3 = a1
# else:
#     a1 = 3      {cond: {1}, a: {1}}
#     {cond: {1}, a: {1}}
#     a2 = a1 + 1 {cond: {1}, a: {2}}
#     ; a3 = a2
# {cond: {1}, a: {3}}     insertion for a
# a4 = a3 + 1  {cond: {1}, a: {4}}


# prog var: a
# dsa var: a1, a2

# trying to build a context:
# 1. merge predecessors context
#     - if a prog var is present in all predecessors
#         - take the intersection of the incarnations
#         - if set is empty
#             - insert join
#         - use some value from the intersection


def make_dsa_var(v: ProgVar, inc: IncarnationNum) -> DSAVar:
    return Var(make_dsa_var_name(v.name, inc), v.typ)


def apply_incarnations(
        s: DSABuilder,
        context: Mapping[ProgVar, Set[IncarnationNum]],
        root: Expr[ProgVarName]) -> Expr[DSAVarName]:

    if isinstance(root, ExprNum):
        return root
    elif isinstance(root, ExprVar):
        var: ProgVar = Var(root.name, root.typ)

        if var not in context:
            # the variable wasn't defined in *any* predecessor
            # however, this might be fine, for example:
            #
            # int a; if (0) return a + 1;
            incarnation_number = IncarnationBase
            print(
                f"WARNING: reading from variable {var} that is never defined")
        else:
            incarnation_number = max(context[var])

        dsa_name = make_dsa_var_name(root.name, incarnation_number)

        return ExprVar(root.typ, name=dsa_name)
    elif isinstance(root, ExprOp):
        return ExprOp(root.typ, Operator(root.operator), operands=tuple(
            apply_incarnations(s, context, operand) for operand in root.operands
        ))
    elif isinstance(root, ExprType | ExprSymbol):
        return root
    assert_never(root)


def get_next_dsa_var_incarnation_number(s: DSABuilder, current_node: NodeName, var: ProgVar) -> IncarnationNum:
    max_inc_num: IncarnationNum = 0
    if current_node in s.insertions and var in s.insertions[current_node]:
        max_inc_num = s.insertions[current_node][var]

    for pred_name in s.original_func.acyclic_preds_of(current_node):
        if var not in s.incarnations[pred_name]:
            continue
        for inc in s.incarnations[pred_name][var]:
            if inc > max_inc_num:
                max_inc_num = inc

    return max_inc_num + 1


def get_next_dsa_var_incarnation_number_from_context(s: DSABuilder, context: Mapping[ProgVar, set[IncarnationNum]], var: ProgVar) -> IncarnationNum:
    if var in context:
        return max(context[var]) + 1
    return 1


K = TypeVar('K')


def set_intersection(it: Iterator[set[K]]) -> set[K]:
    acc = next(it)
    for s in it:
        acc = acc.intersection(s)
    return acc


def set_union(it: Iterator[set[K]]) -> set[K]:
    acc = next(it)
    for s in it:
        acc = acc.union(s)
    return acc


def apply_insertions(s: DSABuilder):
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
                old_incarnation_number = max(
                    s.incarnations[pred_name][prog_var])

                updates.append(Update(make_dsa_var(prog_var, new_incarnation_number),
                                      ExprVar(prog_var.typ, name=make_dsa_var_name(prog_var.name, old_incarnation_number))))
            if len(updates) == 0:
                continue

            j += 1
            join_node_name = NodeName(f'j{j}')
            pred = s.dsa_nodes[pred_name]
            if isinstance(pred, CondNode):
                assert node_name in (pred.succ_then, pred.succ_else)
                if node_name == pred.succ_then:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_then=join_node_name)
                else:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_else=join_node_name)
            elif isinstance(pred, BasicNode | EmptyNode | CallNode):
                # carefull, type hints for dataclasses.replace are too
                # permissive right now
                s.dsa_nodes[pred_name] = dataclasses.replace(
                    pred, succ=join_node_name)
            else:
                assert_never(pred)

            assert len(updates) > 0, f"{node_insertions=}"
            join_node = BasicNode(tuple(updates), node_name)
            s.dsa_nodes[join_node_name] = join_node


def recompute_loops_post_dsa(s: DSABuilder, dsa_loop_targets: Mapping[NodeName, tuple[DSAVar, ...]], new_cfg: CFG) -> Mapping[NodeName, Loop[DSAVarName]]:
    """ Update the loop nodes (because dsa inserts some joiner nodes)
    but keep everything else the same (in particular the loop targets are still ProgVarName!)
    """
    assert_single_loop_header_per_loop(new_cfg)

    # loop header => loop nodes
    all_loop_nodes: dict[LoopHeaderName, tuple[NodeName, ...]] = {}
    for back_edge in new_cfg.back_edges:
        _, loop_header = back_edge
        loop_nodes = compute_natural_loop(new_cfg, back_edge)

        assert all(loop_header in new_cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        all_loop_nodes[loop_header] = loop_nodes

    assert all_loop_nodes.keys() == s.original_func.loops.keys(
    ), "loop headers should remain the same through DSA transformation"

    loops: dict[NodeName, Loop[DSAVarName]] = {}
    for loop_header, loop_nodes in all_loop_nodes.items():
        assert set(s.original_func.loops[loop_header].nodes).issubset(
            loop_nodes), "dsa only inserts joiner nodes, all previous loop nodes should still be loop nodes"
        loops[loop_header] = Loop(back_edge=s.original_func.loops[loop_header].back_edge,
                                  targets=dsa_loop_targets[loop_header],
                                  nodes=loop_nodes)
    return loops


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

    q = [func.cfg.entry]

    visited: set[NodeName] = set()

    s = DSABuilder(original_func=func, insertions={},
                   dsa_nodes={}, incarnations={})

    entry_incarnations: dict[ProgVar, set[IncarnationNum]] = {}
    dsa_args: list[DSAVar] = []
    for arg in func.arguments:
        dsa_args.append(make_dsa_var(arg, IncarnationBase))
        entry_incarnations[arg] = {IncarnationBase}

    assert len(set(unpack_dsa_var_name(arg.name)[0] for arg in dsa_args)) == len(
        dsa_args), "unexpected duplicate argument name"

    # this is hack to deal with the weird assert False() node
    for n in func.nodes:
        preds = func.cfg.all_preds[n]
        if len(preds) == 0 and n != func.cfg.entry:
            node = func.nodes[n]
            assert isinstance(node, CondNode) and node.expr == ExprOp(
                TypeBuiltin(Builtin.BOOL), Operator.FALSE, tuple()), "different weird case in c parser"
            s.dsa_nodes[n] = cast(CondNode[DSAVarName], node)
            visited.add(n)
            # if we can reach this annoying assert False, that means we must
            # be able to reach Err.
            visited.add(NodeNameErr)
            s.incarnations[n] = {}

    dsa_loop_targets: dict[NodeName, tuple[DSAVar, ...]] = {}

    while q:
        current_node = q.pop(-1)
        if current_node in visited:
            continue

        if current_node == NodeNameErr or current_node == NodeNameRet:
            visited.add(current_node)
            continue

        # visit in topolocial order ignoring back edges
        if not all(p in visited for p in func.acyclic_preds_of(current_node)):
            continue

        visited.add(current_node)

        # build up a context (map from prog var to incarnation numbers)
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
                var_defined_on_all_predecessors: bool = all(
                    var in s.incarnations[p] for p in s.original_func.acyclic_preds_of(current_node))

                if not var_defined_on_all_predecessors:
                    # TODO: store this and then perform better analysis to
                    # output clear error message
                    print(
                        f'WARNING: variable {var} not defined on all predecessor of node {current_node}')
                    print(
                        f'1. This might not be an issue if it\'s not used later on (TODO: we can work this out ourselves)')
                    print(
                        f'2. This might not be an issue if all paths on which it isn\'t defined are impossible')
                    print(
                        f'(2. is harder to work out because we need to reason about the program)')

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
                dsa_targets: list[DSAVar] = []

                for target in func.loops[loop_header].targets:
                    # havoc the loop targets
                    fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                        s, current_node, target)
                    context[target] = {fresh_incarnation_number}
                    dsa_targets.append(make_dsa_var(
                        target, fresh_incarnation_number))

                dsa_loop_targets[current_node] = tuple(dsa_targets)

        added_incarnations: dict[ProgVar, DSAVar] = {}

        print(f'{current_node=}')
        print(f'{curr_node_insertions=}')
        for var in context:
            print(
                f'  {var.name}', context[var], '  [joiner]' if curr_node_insertions and var in curr_node_insertions else '')

        node = func.nodes[current_node]
        if isinstance(node, BasicNode):
            upds: list[Update[DSAVarName]] = []
            for upd in node.upds:
                # notice that we don't take into consideration the previous
                # updates from the same node. That's because the updates are
                # simultaneous.
                expr = apply_incarnations(s, context, upd.expr)
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, upd.var)
                dsa_var = make_dsa_var(upd.var, inc)
                upds.append(Update(dsa_var, expr))
                assert upd.var not in added_incarnations, "duplicate updates in BasicNode"
                added_incarnations[upd.var] = dsa_var

            s.dsa_nodes[current_node] = BasicNode(tuple(upds), succ=node.succ)
        elif isinstance(node, CondNode):
            s.dsa_nodes[current_node] = CondNode(
                expr=apply_incarnations(s, context, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, CallNode):
            args = tuple(apply_incarnations(s, context, arg)
                         for arg in node.args)

            rets: list[DSAVar] = []
            for ret in node.rets:
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, ret)
                rets.append(make_dsa_var(ret, inc))
                added_incarnations[ret] = rets[-1]

            s.dsa_nodes[current_node] = CallNode(
                succ=node.succ,
                args=args,
                rets=tuple(rets),
                fname=node.fname,
            )
        elif isinstance(node, EmptyNode):
            s.dsa_nodes[current_node] = node
        else:
            assert_never(node)

        print("  + ")
        for var, incs in added_incarnations.items():
            print(f'  {var.name}', incs.name[1])

        curr_node_incarnations = dict(context)
        for prog_var, dsa_var in added_incarnations.items():
            _, incarnation_number = unpack_dsa_var_name(dsa_var.name)
            curr_node_incarnations[prog_var] = {incarnation_number}
        s.incarnations[current_node] = curr_node_incarnations

        succs = func.cfg.all_succs[current_node]
        for succ in succs:
            if (current_node, succ) not in func.cfg.back_edges:
                q.append(succ)

    apply_insertions(s)

    assert len(visited) == num_reachable(
        func.cfg), f"{visited=} {len(visited)=} {num_reachable(func.cfg)=} {func.cfg.all_succs=} {func.name}"

    # need to recompute the cfg from dsa_nodes
    all_succs = compute_all_successors_from_nodes(s.dsa_nodes)
    cfg = compute_cfg_from_all_succs(all_succs, func.cfg.entry)

    loops = recompute_loops_post_dsa(s, dsa_loop_targets, cfg)

    return Function[DSAVarName](
        cfg=cfg,
        arguments=tuple(dsa_args),
        loops=loops,
        name=func.name,
        nodes=s.dsa_nodes)
