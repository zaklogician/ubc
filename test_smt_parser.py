import smt_parser
import parser_combinator as pc
import smt
import source
import glob


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


def test_parse_decl_fun_model() -> None:
    f = smt_parser.parse_define_fun_model()
    maybeFunModel = pc.parse(f, "(define-fun blah () Bool true)")
    assert not isinstance(maybeFunModel, pc.ParseError)
    (funModel, s) = maybeFunModel
    assert funModel.decl_fn == smt.CmdDeclareFun(
        symbol=smt.Identifier("blah"), arg_sorts=[], ret_sort=source.type_bool)
    assert funModel.expr == source.expr_true
    assert s == ''


def test_parse_model() -> None:
    f = smt_parser.parse_model()
    maybeModel = pc.parse(f,
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
    assert not isinstance(maybeModel, pc.ParseError)
    (model, s) = maybeModel
    assert len(model.sat_unsats) == 2
    assert len(model.decl_models) == 21
    assert s.isspace()

    maybeModel = pc.parse(f,
                          """
        sat
        sat
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
    assert not isinstance(maybeModel, pc.ParseError)

    maybeModel = pc.parse(f,
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
    assert not isinstance(maybeModel, pc.ParseError)


def test_should_parse_files() -> None:
    fn = smt_parser.parse_model()
    for file in glob.glob("./tests/smt/pass/*.smt"):
        with open(file, "r") as f:
            data = f.read()
            maybeModels = pc.parse(fn, data)
            assert not isinstance(maybeModels, pc.ParseError)
