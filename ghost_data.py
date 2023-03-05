from functools import reduce
from types import NoneType
from typing import Callable, Self, NamedTuple, TypeAlias, assert_never
from dataclasses import dataclass
import source

conj = source.expr_and
disj = source.expr_or
imp = source.expr_implies

udiv = source.expr_udiv
mul = source.expr_mul
plus = source.expr_plus
sub = source.expr_sub

slt = source.expr_slt
sle = source.expr_sle
eq = source.expr_eq

T = source.expr_true
F = source.expr_false


class RetMarker(NamedTuple):
    pass


class Integer(NamedTuple):
    pass


FlatType: TypeAlias = Integer


class FlatNode(NamedTuple):
    typ: FlatType
    variable_name: str


class RetFlatNode(NamedTuple):
    typ: FlatType


class AccessLeafNode(NamedTuple):
    variable_name: str
    field_name: str
    parent: 'AccessNode'


class RetAccessLeafNode(NamedTuple):
    field_name: str
    parent: 'AccessNode'


class FinalNode(NamedTuple):
    inner: AccessLeafNode | RetAccessLeafNode | RetFlatNode | FlatNode


@dataclass(frozen=True)
class AccessNode():
    struct_name: str
    parent: None | Self = None  # type:ignore

    def saccess(self: 'AccessNode', struct_name: str) -> 'AccessNode':
        return AccessNode(struct_name, self)

    s = saccess

    def vaccess(self, field: str) -> Callable[[str | RetMarker], FinalNode]:
        def fn(inp: str | RetMarker) -> FinalNode:
            if isinstance(inp, str):
                return FinalNode(AccessLeafNode(inp, field, self))
            return FinalNode(RetAccessLeafNode(field, self))
        return fn
    v = vaccess


def struct(struct_name: str) -> AccessNode:
    return AccessNode(struct_name)


def integer() -> Callable[[str | RetMarker], FinalNode]:
    def fn(inp: str | RetMarker) -> FinalNode:
        if isinstance(inp, RetMarker):
            return FinalNode(RetFlatNode(Integer()))
        return FinalNode(FlatNode(Integer(), inp))
    return fn


def ret(fn: Callable[[str | RetMarker], FinalNode]) -> FinalNode:
    return fn(RetMarker())


def humanvar(final_node: FinalNode) -> source.HumanVarName:
    ret_prefix = 'ret__'
    value_suffix = '#v'
    int_str = 'int'

    def variable_prefix(variable: str) -> str:
        return f"{variable}___"

    def struct_prefix(struct_name: str) -> str:
        return f"struct_{struct_name}_C{value_suffix}"

    def struct_access(prev: str, field: str) -> str:
        return f"{prev}.{field}_C"

    def variable_access(prev: str, field: str) -> str:
        return f"{prev}.{field}_C"

    if isinstance(final_node.inner, RetFlatNode | FlatNode):
        assert isinstance(final_node.inner.typ, Integer)
        if isinstance(final_node.inner, RetFlatNode):
            return source.HumanVarName(source.HumanVarNameSubject(ret_prefix + int_str + value_suffix), (), False)
        elif isinstance(final_node.inner, FlatNode):
            return source.HumanVarName(
                source.HumanVarNameSubject(
                    f"{variable_prefix(final_node.inner.variable_name)}{int_str}{value_suffix}"),
                (),
                False
            )
        assert_never(final_node.inner)

    prefix = variable_prefix(final_node.inner.variable_name) if isinstance(
        final_node.inner, AccessLeafNode) else ret_prefix

    nodes: list[AccessLeafNode | AccessNode | RetAccessLeafNode] = []
    curr_node: AccessLeafNode | AccessNode | RetAccessLeafNode | None = final_node.inner
    while curr_node is not None:
        nodes.append(curr_node)
        curr_node = curr_node.parent

    root_struct = nodes.pop()
    nodes = nodes[::-1]

    assert isinstance(root_struct, AccessNode)
    access_str = struct_prefix(root_struct.struct_name)

    for (i, node) in enumerate(nodes):
        if isinstance(node, RetAccessLeafNode | AccessLeafNode):
            assert i == len(nodes) - 1
            access_str = variable_access(access_str, node.field_name)
        elif isinstance(node, AccessNode):
            assert i < len(nodes) - 1
            access_str = struct_access(access_str, node.struct_name)
        else:
            assert_never(node)
    access_str = prefix + access_str
    return source.HumanVarName(source.HumanVarNameSubject(access_str), (), False)


def get(file_name: str, func_name: str) -> source.Ghost[source.HumanVarName] | None:
    if file_name.endswith('.c'):
        file_name = file_name[:-len('.c')] + '.txt'
    if file_name in universe and func_name in universe[file_name]:
        return universe[file_name][func_name]
    return None


def conjs(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    # pyright is stupid, but mypy works it out (we only care about mypy)
    return reduce(source.expr_and, xs)  # pyright: ignore


def i32(n: int) -> source.ExprNumT:
    assert -0x8000_0000 <= n and n <= 0x7fff_ffff
    return source.ExprNum(source.type_word32, n)


def i32v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word32, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def i64v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word64, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def i64(n: int) -> source.ExprNumT:
    assert -0x8000_0000_0000_0000 <= n and n <= 0x7fff_ffff_ffff_ffff
    return source.ExprNum(source.type_word64, n)


def g(name: str) -> source.ExprVarT[source.HumanVarName]:
    """ guard """
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=True, path=()))


i32ret = source.ExprVar(source.type_word32, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))

i64ret = source.ExprVar(source.type_word64, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))


def sbounded(var: source.ExprVarT[source.HumanVarName], lower: source.ExprT[source.HumanVarName], upper: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    return conj(sle(lower, var), sle(var, upper))

# def assigned(var: source.ExprVarT[source.HumanVarName]):
#     return source.ExprAssigned(source.type_bool, var)


def lh(x: str) -> source.LoopHeaderName:
    return source.LoopHeaderName(source.NodeName(x))


def get_abc_post() -> source.ExprT[source.HumanVarName]:
    xret = ret(struct('abc').v('x'))
    val = integer()('val')
    var = humanvar(xret)
    val_var = humanvar(val)
    return eq(source.ExprVar(source.type_word32, val_var), source.ExprVar(source.type_word32, var))


universe = {
    "tests/all.txt": {
        # 3 <= i ==> a = 1
        # 3:w32 <=s i:w32 ==> a:w32 = 1:w32
        "tmp.undefined_var_with_loops": source.Ghost(
            loop_invariants={
                lh("5"): conj(imp(sle(i32(3), i32v("i")), eq(i32v("a"), i32(1))), sbounded(i32v("i"), i32(0), i32(5)))
            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.multiple_loops___fail_missing_invariant": source.Ghost(
            loop_invariants={
                # no need to think, i is always going to be less than 200, and
                # that's enough to prove no overflows
                lh('17'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('4'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('8'): sbounded(i32v('i'), i32(0), i32(200)),

            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.arith_sum": source.Ghost(
            loop_invariants={
                # 0 <= i <= n
                # s = i * (i - 1) / 2
                # i#assigned
                # s#assigned
                lh('5'): conjs(
                    sbounded(i32v('i'), i32(0), i32v('n')),
                    eq(i32v('s'), udiv(mul(i32v('i'), sub(i32v('i'), i32(1))), i32(2))),
                    g('i'),
                    g('s')),
            },
            precondition=sbounded(i32v('n'), i32(0), i32(100)),
            postcondition=eq(i32ret, udiv(
                mul(i32v('n'), sub(i32v('i'), i32(1))), i32(2))),
        ),

        "tmp.multiple_ret_incarnations___fail_missing_invariants": source.Ghost(
            loop_invariants={lh('5'): T},
            precondition=sle(i32(0), i32v('n')),
            postcondition=eq(i32ret, udiv(i32v('n'), i32(2))),
        )
    },
    "./examples/simple.txt": {
        "tmp.get_abc": source.Ghost(
            loop_invariants={},
            precondition=T,
            postcondition=get_abc_post(),
        )
    }
}
