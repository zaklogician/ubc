import smt_parser
import parser_combinator as pc
import smt
import source
import glob
from typing import Literal, Sequence, Callable
import assume_prove as ap


def test_parse_identifier() -> None:
    f = smt_parser.parse_identifier()
    maybeIdentifier = pc.parse(f, "hello")
    assert not isinstance(maybeIdentifier, pc.ParseError)
    (ident, s) = maybeIdentifier
    assert ident == "hello"
    assert s == ''

    maybeIdentifier = pc.parse(f, "123hello")
    assert isinstance(maybeIdentifier, pc.ParseError)


def test_parse_cmd_declare_fun() -> None:
    f = smt_parser.parse_cmd_declare_fun()
    maybeDeclFun = pc.parse(f, "(declare-fun id () Bool)")
    assert not isinstance(maybeDeclFun, pc.ParseError)
    (declFun, s) = maybeDeclFun
    declFunExpected = smt.CmdDeclareFun(symbol=smt.Identifier(
        "id"), arg_sorts=[], ret_sort=source.type_bool)
    assert declFun == declFunExpected
    assert s == ''


def test_parse_op() -> None:
    f = smt_parser.parse_op()
    maybeOp = pc.parse(f, "bvadd")
    assert not isinstance(maybeOp, pc.ParseError)
    (op, s) = maybeOp
    assert op == source.Operator.PLUS
    assert s == ''

    maybeOp = pc.parse(f, "bvsub")
    assert not isinstance(maybeOp, pc.ParseError)
    (op, s) = maybeOp
    assert op == source.Operator.MINUS
    assert s == ''


def test_parse_sorted_var() -> None:
    f = smt_parser.parse_sorted_var()
    maybeSortedVar = pc.parse(f, "(x Bool)")
    assert not isinstance(maybeSortedVar, pc.ParseError)


def test_parse_decl_fun_model() -> None:
    f = smt_parser.parse_model_response()
    maybeFunModel = pc.parse(f, "(define-fun blah () Bool true)")
    assert not isinstance(maybeFunModel, pc.ParseError)
    (funModel, s) = maybeFunModel
    assert funModel == smt.CmdDefineFun(
        symbol=smt.Identifier("blah"), args=[], ret_sort=source.type_bool, term=source.expr_true)
    assert s == ''


def get_bool(val: bool) -> source.ExprT[ap.VarName]:
    if val:
        return source.expr_true
    return source.expr_false


def get_bitvec_from_str(val: str, base: Literal[2, 16]) -> source.ExprT[ap.VarName]:
    val = val[2:]
    intval = int(val, base)
    return source.ExprNum(typ=source.type_word32, num=intval)


def get_model_response(name: str, ty: source.Type, e: source.ExprT[ap.VarName]) -> smt.ModelResponse:
    return smt.ModelResponse(symbol=smt.Identifier(name), args=[], ret_sort=ty, term=e)


def get_bool_fn(name: str, b: bool) -> smt.ModelResponse:
    return get_model_response(name, source.type_bool, get_bool(b))


def get_bvec_fn(name: str, val: str, base: Literal[2, 16]) -> smt.ModelResponse:
    return get_model_response(name, source.type_word32, get_bitvec_from_str(val, base))


def test_parse_model() -> None:
    f = smt_parser.parse_responses()
    maybeResponses = pc.parse(f,
                              """
        sat
        sat
        (model
        (define-fun node_Err_ok () Bool false)
        (define-fun node_Ret_ok () Bool true)
        (define-fun node_2_ok () Bool false)
        (define-fun node_17_ok () Bool false)
        (define-fun node_9_ok () Bool false)
        (define-fun node_8_ok () Bool false)
        (define-fun node_7_ok () Bool true)
        (define-fun node_j2_ok () Bool true)
        (define-fun node_6_ok () Bool false)
        (define-fun node_5_ok () Bool false)
        (define-fun node_j1_ok () Bool false)
        (define-fun node_4_ok () Bool false)
        (define-fun node_3_ok () Bool true)
        (define-fun node_1_ok () Bool true)
        (define-fun a___int@v~1 () (_ BitVec 32) #b10101000000000000000101000000000)
        (define-fun b___int@v~1 () (_ BitVec 32) #b01011100100000000000000000000000)
        (define-fun b___int@v~2 () (_ BitVec 32) #b10011011111111111111011000000000)
        (define-fun a___int@v~3 () (_ BitVec 32) #b00000100100000000000101000000000)
        (define-fun b___int@v~3 () (_ BitVec 32) #b01011100100000000000000000000000)
        (define-fun a___int@v~2 () (_ BitVec 32) #b00000100100000000000101000000000)
        (define-fun ret__int@v~1 () (_ BitVec 32) #b00000000000000000000000000000000)
        )
        """)
    assert not isinstance(maybeResponses, pc.ParseError)
    (responses, s) = maybeResponses
    assert len(responses) == 3
    assert s.isspace()
    assert responses[0] == smt.CheckSatResponse.SAT
    assert responses[1] == smt.CheckSatResponse.SAT
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21

    res = [get_bool_fn("node_Err_ok", False), get_bool_fn("node_Ret_ok", True), get_bool_fn("node_2_ok", False), get_bool_fn("node_17_ok", False), get_bool_fn("node_9_ok", False), get_bool_fn("node_8_ok", False), get_bool_fn("node_7_ok", True), get_bool_fn("node_j2_ok", True), get_bool_fn("node_6_ok", False), get_bool_fn("node_5_ok", False), get_bool_fn("node_j1_ok", False), get_bool_fn("node_4_ok", False), get_bool_fn("node_3_ok", True), get_bool_fn("node_1_ok", True), get_bvec_fn("a___int@v~1", "#b10101000000000000000101000000000", 2), get_bvec_fn("b___int@v~1", "#b01011100100000000000000000000000", 2), get_bvec_fn("b___int@v~2", "#b10011011111111111111011000000000", 2), get_bvec_fn("a___int@v~3", "#b00000100100000000000101000000000", 2), get_bvec_fn("b___int@v~3", "#b01011100100000000000000000000000", 2), get_bvec_fn("a___int@v~2", "#b00000100100000000000101000000000", 2), get_bvec_fn("ret__int@v~1", "#b00000000000000000000000000000000", 2)
           ]

    for out, expected in zip(responses[2], res):
        assert out == expected

    maybeResponses = pc.parse(f,
                              """
        unsat 
        unknown 
        (
          (define-fun node_Ret_ok () Bool
            true)
          (define-fun node_9_ok () Bool
            false)
          (define-fun node_1_ok () Bool
            true)
          (define-fun b___int@v~1 () (_ BitVec 32)
            #x8c044046)
          (define-fun node_17_ok () Bool
            false)
          (define-fun b___int@v~3 () (_ BitVec 32)
            #x12010094)
          (define-fun a___int@v~3 () (_ BitVec 32)
            #x2fdf0018)
          (define-fun node_j2_ok () Bool
            true)
          (define-fun node_3_ok () Bool
            true)
          (define-fun node_4_ok () Bool
            false)
          (define-fun node_8_ok () Bool
            true)
          (define-fun node_Err_ok () Bool
            false)
          (define-fun node_7_ok () Bool
            true)
          (define-fun node_2_ok () Bool
            false)
          (define-fun a___int@v~1 () (_ BitVec 32)
            #xc4048048)
          (define-fun a___int@v~2 () (_ BitVec 32)
            #x2fdf0018)
          (define-fun node_5_ok () Bool
            true)
          (define-fun node_6_ok () Bool
            false)
          (define-fun node_j1_ok () Bool
            true)
          (define-fun ret__int@v~1 () (_ BitVec 32)
            #x00000000)
          (define-fun b___int@v~2 () (_ BitVec 32)
            #x00000000)
        )
        """)
    assert not isinstance(maybeResponses, pc.ParseError)
    (responses, s) = maybeResponses
    assert s.isspace()
    assert len(responses) == 3
    assert responses[0] == smt.CheckSatResponse.UNSAT
    assert responses[1] == smt.CheckSatResponse.UNKNOWN
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21

    res = [
        get_bool_fn("node_Ret_ok", True),
        get_bool_fn("node_9_ok", False),
        get_bool_fn("node_1_ok", True),
        get_bvec_fn("b___int@v~1", "#x8c044046", 16),
        get_bool_fn("node_17_ok", False),
        get_bvec_fn("b___int@v~3", "#x12010094", 16),
        get_bvec_fn("a___int@v~3", "#x2fdf0018", 16),
        get_bool_fn("node_j2_ok", True),
        get_bool_fn("node_3_ok", True),
        get_bool_fn("node_4_ok", False),
        get_bool_fn("node_8_ok", True),
        get_bool_fn("node_Err_ok", False),
        get_bool_fn("node_7_ok", True),
        get_bool_fn("node_2_ok", False),
        get_bvec_fn("a___int@v~1", "#xc4048048", 16),
        get_bvec_fn("a___int@v~2", "#x2fdf0018", 16),
        get_bool_fn("node_5_ok", True),
        get_bool_fn("node_6_ok", False),
        get_bool_fn("node_j1_ok", True),
        get_bvec_fn("ret__int@v~1", "#x00000000", 16),
        get_bvec_fn("b___int@v~2", "#x00000000", 16)
    ]

    maybeResponses = pc.parse(f,
                              """
        sat
        sat
        (
        (define-fun node_Err_ok () Bool false)
        (define-fun node_Ret_ok () Bool true)
        (define-fun node_2_ok () Bool false)
        (define-fun node_17_ok () Bool false)
        (define-fun node_9_ok () Bool false)
        (define-fun node_8_ok () Bool true)
        (define-fun node_7_ok () Bool true)
        (define-fun node_j2_ok () Bool true)
        (define-fun node_6_ok () Bool false)
        (define-fun node_5_ok () Bool false)
        (define-fun node_j1_ok () Bool false)
        (define-fun node_4_ok () Bool false)
        (define-fun node_3_ok () Bool true)
        (define-fun node_1_ok () Bool true)
        (define-fun a___int@v~1 () (_ BitVec 32) #b10000000000000001111010001100010)
        (define-fun b___int@v~1 () (_ BitVec 32) #b00000000000000000000101111011110)
        (define-fun b___int@v~2 () (_ BitVec 32) #b00000000000000000000000000000000)
        (define-fun a___int@v~3 () (_ BitVec 32) #b10000000000000010000000001000000)
        (define-fun b___int@v~3 () (_ BitVec 32) #b00000000000000000000101111011110)
        (define-fun a___int@v~2 () (_ BitVec 32) #b10000000000000010000000001000000)
        (define-fun ret__int@v~1 () (_ BitVec 32) #b00000000000000000000000000000000)
        )""")
    assert not isinstance(maybeResponses, pc.ParseError)
    assert s.isspace()
    (responses, s) = maybeResponses
    assert len(responses) == 3
    assert responses[0] == smt.CheckSatResponse.SAT
    assert responses[1] == smt.CheckSatResponse.SAT
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21


def test_should_parse_files() -> None:
    fn = smt_parser.parse_responses()
    for file in glob.glob("./tests/smt/pass/*.smt"):
        with open(file, "r") as f:
            data = f.read()
            maybeModels = pc.parse(fn, data)
            assert not isinstance(maybeModels, pc.ParseError)
