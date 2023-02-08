import parser_combinator as pc


def test_many() -> None:
    f = pc.many(pc.digit())
    maybeVal = pc.parse(f, "12345")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == [1, 2, 3, 4, 5]
    assert s == ''


def test_integer() -> None:
    f = pc.integer()
    maybeVal = pc.parse(f, "12345")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == 12345
    assert s == ''

    maybeVal = pc.parse(f, "")
    assert isinstance(maybeVal, pc.ParseError)


def test_char() -> None:
    f = pc.char('a')
    maybeVal = pc.parse(f, "abc")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == 'a'
    assert s == "bc"


def test_between() -> None:
    f = pc.between(pc.char('('), pc.string("hello"), pc.char(')'))
    maybeVal = pc.parse(f, "(hello)")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == "hello"
    assert s == ''


def test_array() -> None:
    f = pc.array(pc.char('['), pc.integer(), pc.char(']'), pc.char(','))
    maybeVal = pc.parse(f, "[1,2,3,4,5]")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == [1, 2, 3, 4, 5]
    assert s == ''

    f = pc.array(pc.char('('), pc.integer(), pc.char(')'), pc.many1(
        pc.choice([pc.space(), pc.tab(), pc.newline(), pc.carriage_return()])))
    maybeVal = pc.parse(f, "(1  2\t3\n4 \t 5\r6)")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == [1, 2, 3, 4, 5, 6]
    assert s == ''

    maybeVal = pc.parse(f, "()")
    assert not isinstance(maybeVal, pc.ParseError)
    (val, s) = maybeVal
    assert val == []
    assert s == ''


def test_regex() -> None:
    pass
