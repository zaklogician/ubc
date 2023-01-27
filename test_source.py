from typing import Sequence
import pytest
import source


w64 = source.type_word64
w32 = source.type_word32
bol = source.type_bool
ops = source.Operator

# quick and dirty (but my first :)) s-expr parser to check things involving
# expressions.
#
# Operators, numbers and variables can be followed by a :xxx to specify the type
# see parse_typ for supported typ
#
# Be careful, there is no type checking, only type inference for convenience


def try_parse_number(s: str) -> tuple[source.ExprT[str] | None, str]:
    # print('parse_number in', repr(s))
    if not (len(s) >= 1 and s[0].isdigit() or (len(s) >= 2 and s[0] == '-' and s[1].isdigit())):
        return None, s

    i = 1
    while i < len(s) and s[i].isdigit():
        i += 1

    num = int(s[:i])
    if i < len(s) and s[i] == ':':
        typ, s = parse_typ(s[i + 1:])
    else:
        typ = source.type_word32
        s = s[i:]
    return source.ExprNum(typ, num), s


def parse_operator(s: str) -> tuple[source.Operator, str]:
    if len(s) == 0:
        raise ValueError("expected operator, reached eof")

    i = 0
    while i < len(s) and not s[i].isspace() and s[i] != ')' and s[i] != ':':
        i += 1
    return source.Operator(s[:i]), s[i:]


def consume_space(s: str) -> str:
    while len(s) > 0 and s[0].isspace():
        s = s[1:]
    return s


def parse_typ(s: str) -> tuple[source.Type, str]:
    i = 0
    while i < len(s) and not s[i].isspace() and s[i] != ')':
        i += 1
    typ = s[:i]
    s = s[i:]

    if typ == 'w32':
        return source.type_word32, s
    if typ == 'w64':
        return source.type_word64, s
    if typ == 'bool':
        return source.type_bool, s
    raise ValueError(f"type {typ} not supported")


def try_parse_var(s: str) -> tuple[source.ExprVarT[str] | None, str]:
    # print('try parse var in', repr(s))
    # var is of the form `name:type`
    if len(s) == 0 or s[0].isdigit() or s[0] == '(':
        return None, s

    i = 0
    while i < len(s) and not s[i].isspace() and s[i] != ')' and s[i] != ':':
        i += 1

    if i >= len(s) or s[i] != ':':
        return None, s  # fail to parse var

    var_name = s[:i]
    typ, s = parse_typ(s[i + 1:])
    return source.ExprVar(typ, var_name), s


def consume_char(s: str, char: str) -> str:
    assert len(char) == 1
    if len(s) == 0:
        raise ValueError(f"expected {char!r}, got eof")
    if s[0] != char:
        raise ValueError(f"expected {char!r}, got {s[0]!r}")
    return s[1:]


def type_inference(operator: source.Operator, operands: Sequence[source.ExprT[str]]) -> source.Type:
    if operator in (ops.AND, ops.OR, ops.IMPLIES):
        if len(operands) != 2:
            raise ValueError(f"operator {operator} is a _binary_ operator")
        if not all(op.typ == source.type_bool for op in operands):
            raise ValueError(
                f"operands of {operator} should be of boolean type")
        return source.type_bool
    elif operator in (ops.PLUS, ops.MINUS, ops.TIMES, ops.DIVIDED_BY, ops.MODULUS, ops.LESS, ops.LESS_EQUALS, ops.SIGNED_LESS, ops.SIGNED_LESS_EQUALS, ops.EQUALS):
        if len(operands) != 2:
            raise ValueError(f"operator {operator} is a _binary_ operator")

        types = set(operand.typ for operand in operands)
        if len(types) >= 2:
            raise ValueError(
                f"all operands of {operator} should have the same type (got {types})")

        if operator in (ops.LESS, ops.LESS_EQUALS, ops.SIGNED_LESS, ops.SIGNED_LESS_EQUALS, ops.EQUALS):
            return bol
        return operands[0].typ
    elif operator is ops.IF_THEN_ELSE:
        if len(operands) != 3:
            raise ValueError(f"IfThenElse should have three operands")
        if not operands[0].typ == bol:
            raise ValueError(f"first operand of IfThenElse should be boolean")
        if not operands[1].typ == operands[2].typ:
            raise ValueError(
                f"2nd and 3rd operands of IfThenElse should have the same type, got {operands[1].typ} and {operands[2].typ}")
        return operands[1].typ
    elif operator in (ops.TRUE, ops.FALSE):
        if len(operands) != 0:
            raise ValueError("true and false operator don't take any operands")
        return bol
    elif operator is ops.NOT:
        if len(operands) != 1:
            raise ValueError("not is a _unary_ operator")
        if operands[0].typ != bol:
            raise ValueError("operands to Not should be boolean")
        return bol
    else:
        raise ValueError(f"unsupported operator {operator}")


def parse_sexpr(s: str) -> tuple[source.ExprT[str], str]:
    # print('parse_expr in', repr(s))
    s = consume_space(s)
    maybe_num, s = try_parse_number(s)
    if maybe_num is not None:
        return maybe_num, s

    maybe_var, s = try_parse_var(s)
    if maybe_var is not None:
        return maybe_var, s

    s = consume_char(s, '(')

    operator, s = parse_operator(s)
    operator_typ: source.Type | None = None
    if len(s) > 0 and s[0] == ':':
        operator_typ, s = parse_typ(s[1:])

    s = consume_space(s)
    operands: list[source.ExprT[str]] = []
    while len(s) > 0 and s[0] != ')':
        operand, s = parse_sexpr(s)
        operands.append(operand)
        s = consume_space(s)

    s = consume_char(s, ')')

    if operator_typ is None:
        operator_typ = type_inference(operator, operands)

    return source.ExprOp(operator_typ, operator, tuple(operands)), s


def parse_full_sexpr(s: str) -> source.ExprT[str]:
    expr, rest = parse_sexpr(s)
    assert len(rest) == 0, f"got left overs in sexpr {rest!r}"
    return expr


# not sure why mypy sometimes need an explicit type hint...
@pytest.mark.parametrize('s, expected', (
    ('(Plus 1 2)', source.ExprOp(w32, ops.PLUS,
                                 (source.ExprNum(w32, 1), source.ExprNum(w32, 2)))),
    ('(Plus 1:w64 2:w64)', source.ExprOp(w64, ops.PLUS,
                                         (source.ExprNum(w64, 1), source.ExprNum(w64, 2)))),
    ('(Plus 1:w64 2:w64)', source.ExprOp(w64, ops.PLUS,
                                         (source.ExprNum(w64, 1), source.ExprNum(w64, 2)))),
    ('(Minus 3 4)', source.ExprOp(w32, ops.MINUS,
                                  (source.ExprNum(w32, 3), source.ExprNum(w32, 4)))),
    ('(Plus (Minus 3 4) 5)', source.ExprOp[source.Type, str](w32, ops.PLUS,
                                                             (parse_full_sexpr('(Minus 3 4)'), source.ExprNum(w32, 5)))),
    ('(Equals 2 3)', source.ExprOp[source.Type, str](bol, ops.EQUALS,
                                                     (source.ExprNum(w32, 2), source.ExprNum(w32, 3)))),
    ('(IfThenElse (Equals 2 3) a:w64 b:w64)', source.ExprOp[source.Type, str](w64, ops.IF_THEN_ELSE,
                                                                              (parse_full_sexpr("(Equals 2 3)"), source.ExprVar(w64, 'a'), source.ExprVar(w64, 'b')))),
    ('(IfThenElse (Equals 2 3) a:w64 b:w64)', parse_full_sexpr(
        '(IfThenElse:w64 (Equals:bool 2:w32 3:w32) a:w64 b:w64)')),
    ('(IfThenElse (Equals 2 3) a:w64 (IfThenElse (Equals 3 4) b:w64 c:w64))',
        source.ExprOp[source.Type, str](w64, ops.IF_THEN_ELSE, (parse_full_sexpr("(Equals 2 3)"), source.ExprVar(w64, 'a'), parse_full_sexpr('(IfThenElse (Equals 3 4) b:w64 c:w64)')))),
))
def test_sexpr_parser(s: str, expected: source.ExprT[str]) -> None:
    assert parse_full_sexpr(s) == expected


@pytest.mark.parametrize('expr_str, sub_str, cond_str', (
    ('(Plus a:w32 b:w32)', 'a:w32', '(True)'),
    ('(Plus a:w32 b:w32)', 'b:w32', '(True)'),
    ('(Plus a:w32 b:w32)', 'c:w32', '(False)'),

    ('(IfThenElse (Equals a:w32 1) b:w32 c:w32)', 'b:w32', '(Equals a:w32 1)'),
    ('(IfThenElse (Equals a:w32 1) b:w32 c:w32)', 'c:w32', '(Not (Equals a:w32 1))'),
    ('(IfThenElse (Equals a:w32 1) b:w32 c:w32)', 'a:w32', '(True)'),

    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool yy:w32 z:w32))',
     'x:w32', '(And a:bool b:bool)'),
    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool yy:w32 z:w32))',
     'y:w32', '(And a:bool (Not b:bool))'),
    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool yy:w32 z:w32))',
     'yy:w32', '(And (Not a:bool) c:bool)'),
    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool yy:w32 z:w32))',
     'z:w32', '(And (Not a:bool) (Not c:bool))'),

    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool y:w32 x:w32))',
     'x:w32', '(Or (And a:bool b:bool) (And (Not a:bool) (Not c:bool)))'),
    ('(IfThenElse a:bool (IfThenElse b:bool x:w32 y:w32) (IfThenElse c:bool y:w32 x:w32))',
     'y:w32', '(Or (And a:bool (Not b:bool)) (And (Not a:bool) c:bool))'),

    ('(IfThenElse (Equals x:w32 1) x:w32 2)', 'x:w32', '(True)'),

    ('(IfThenElse (IfThenElse a:bool b:bool c:bool) (Or b:bool d:bool) (False))',
     'b:bool', '(Or a:bool (IfThenElse a:bool b:bool c:bool))'),
))
def test_condition_to_evaluate_subexpr_in_expr(expr_str: str, sub_str: str, cond_str: str) -> None:
    expr, sub, cond = parse_full_sexpr(expr_str), parse_full_sexpr(
        sub_str), parse_full_sexpr(cond_str)

    # more convenient for debugging
    assert source.pretty_expr_ascii(source.condition_to_evaluate_subexpr_in_expr(
        expr, sub)) == source.pretty_expr_ascii(cond)
    assert source.condition_to_evaluate_subexpr_in_expr(expr, sub) == cond


if __name__ == "__main__":
    expr = parse_full_sexpr("(Plus (Minus 2 a:w32) 1)")
    print(expr)
    print(source.pretty_expr_ascii(expr))
