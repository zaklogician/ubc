import typing as tp
from typing_extensions import NamedTuple
import re


class ParseError(NamedTuple):
    msg: str


T = tp.TypeVar('T')
K = tp.TypeVar('K')
V = tp.TypeVar('V')
S = tp.TypeVar('S')

ParseResult: tp.TypeAlias = tp.Tuple[T, str] | ParseError
Parser = tp.Callable[[str], ParseResult[T]]


def pmap(p: Parser[T], f: tp.Callable[[T], K]) -> Parser[K]:
    def fn(s: str) -> ParseResult[K]:
        maybeVal = p(s)
        if isinstance(maybeVal, ParseError):
            return maybeVal
        (val, s) = maybeVal
        newVal = f(val)
        return (newVal, s)
    return fn


def parse(p: Parser[T], s: str) -> ParseResult[T]:
    maybeVal = p(s)
    if isinstance(maybeVal, ParseError):
        return maybeVal
    (t, s) = maybeVal
    return (t, s)


def char(c: str) -> Parser[str]:
    assert len(c) == 1

    def fn(s: str) -> ParseResult[str]:
        if len(s) < 1:
            return ParseError(f"expected {c} but received EOF")
        elif s[0] != c:
            return ParseError(f"expected {c} but received {s[0]}")
        return (s[0], s[1:])
    return fn


def space() -> Parser[None]:
    def fn(s: str) -> ParseResult[None]:
        if len(s) < 1:
            return ParseError("space called with string of length != 1")

        elif s[0] == ' ':
            return (None, s[1:])

        return ParseError(f"expected space but got {s[0]}")

    return fn


def tab() -> Parser[None]:
    def fn(s: str) -> ParseResult[None]:
        if len(s) < 1:
            return ParseError("tab called with string of length != 1")
        elif s[0] == '\t':
            return (None, s[1:])
        return ParseError(f"expected tab but got {s[0]}")
    return fn


def carriage_return() -> Parser[None]:
    def fn(s: str) -> ParseResult[None]:
        if len(s) < 1:
            return ParseError("carriage_return called with string of length != 1")
        elif s[0] == '\r':
            return (None, s[1:])
        return ParseError(f"expected carriage return but got {s[0]}")
    return fn


def newline() -> Parser[None]:
    def fn(s: str) -> ParseResult[None]:
        if len(s) < 1:
            return ParseError("newline expected but got EOF")
        elif s[0] == '\n':
            return (None, s[1:])
        return ParseError(f"expected newline but got {s[0]}")

    return fn


def digit() -> Parser[int]:
    def fn(s: str) -> ParseResult[int]:
        if len(s) < 1:
            return ParseError("expected digit but got EOF")
        if not s[0].isdigit():
            return ParseError(f"expected digit but got {s[0]}")
        return (int(s[0]), s[1:])
    return fn


def string(expected: str) -> Parser[str]:
    def fn(inp: str) -> ParseResult[str]:
        if len(inp) == 0:
            return ParseError("expected {0} but got EOF".format(expected))
        if not inp.startswith(expected):
            return ParseError("expected {0} but input does not contain this string".format(expected))

        return (expected, inp[len(expected):])
    return fn


def compose(p1: Parser[T], p2: Parser[K]) -> Parser[tp.Tuple[T, K]]:
    def fn(s: str) -> ParseResult[tp.Tuple[T, K]]:
        maybeVal1 = p1(s)
        if isinstance(maybeVal1, ParseError):
            return maybeVal1
        (t, s) = maybeVal1

        maybeVal2 = p2(s)

        if isinstance(maybeVal2, ParseError):
            return maybeVal2

        (k, s) = maybeVal2
        return ((t, k), s)
    return fn


def choice(ps: tp.Sequence[Parser[T]]) -> Parser[T]:
    def fn(s: str) -> ParseResult[T]:
        firstError: None | ParseError = None
        # user error if this fails
        assert len(ps) > 1
        for p in ps:
            maybeVal = p(s)
            if not isinstance(maybeVal, ParseError):
                return maybeVal
            if firstError == None:
                firstError = maybeVal
        # reaching here implies this is always true
        assert isinstance(firstError, ParseError)
        return firstError
    return fn


def between(lhs: Parser[K], p: Parser[V], rhs: Parser[T]) -> Parser[V]:
    """consumes lhs, parses p and then consumes rhs, any error occurring at any stage will also end up munching the string"""
    def fn(s: str) -> ParseResult[V]:
        maybeLhs = lhs(s)
        if isinstance(maybeLhs, ParseError):
            return maybeLhs
        (_, s) = maybeLhs
        maybeVal = p(s)
        if isinstance(maybeVal, ParseError):
            return maybeVal
        (val, s) = maybeVal
        maybeRhs = rhs(s)
        if isinstance(maybeRhs, ParseError):
            return maybeRhs
        (_, s) = maybeRhs
        return (val, s)
    return fn


def many(p: Parser[T]) -> Parser[list[T]]:
    """consumes p repeatedly until an error occurs, the string will be processed up until the last successful parse"""
    def fn(s: str) -> ParseResult[list[T]]:
        res: list[T] = []
        while True:
            maybeVal = p(s)
            if isinstance(maybeVal, ParseError):
                return (res, s)
            (val, s) = maybeVal
            res.append(val)
    return fn


def many1(p: Parser[T]) -> Parser[tp.Sequence[T]]:
    def fn(s: str) -> ParseResult[tp.Sequence[T]]:
        maybePs = many(p)(s)
        assert not isinstance(maybePs, ParseError)
        (ps, s) = maybePs
        if len(ps) == 0:
            return ParseError("parser expected at least one element")
        return (ps, s)
    return fn


def try_and_ignore(p: Parser[T]) -> Parser[None]:
    def fn(s: str) -> ParseResult[None]:
        maybeVal = p(s)
        if isinstance(maybeVal, ParseError):
            return (None, s)
        (_, s) = maybeVal
        return (None, s)
    return fn


def integer() -> Parser[int]:
    def fn(s: str) -> ParseResult[int]:
        maybeVal = many1(digit())(s)
        if isinstance(maybeVal, ParseError):
            return maybeVal
        (ds, s) = maybeVal
        summed = 0
        for power, curr_digit in enumerate(reversed(ds)):
            summed += curr_digit*(10**power)
        return (summed, s)
    return fn


def ws() -> Parser[int]:
    """a specialised parser to handle pc.many(pc.choice([pc.space(), pc.tab(), pc.carriage_return()])), returns a count of whitespace characters"""

    def is_whitespace(ch: str) -> bool:
        if ch[0] == ' ' or ch[0] == '\r' or ch[0] == '\t' or ch[0] == '\n':
            return True
        return False

    def fn(s: str) -> ParseResult[int]:
        if len(s) == 0:
            return (0, s)
        index = 0
        while True:
            if index >= len(s):
                break
            if not is_whitespace(s[index]):
                break
            index += 1
        assert len(s) >= index
        s = s[index:]
        return (index, s)

    return fn


def without_ws(p: Parser[T]) -> Parser[T]:
    fn: tp.Callable[[tp.Tuple[int, T]], T] = lambda x: x[1]
    return pmap(compose(ws(), p), fn)


def regex(regex: re.Pattern[str]) -> Parser[str]:
    def fn(s: str) -> ParseResult[str]:
        m = regex.search(s)
        errmsg = "was not able to find regex pattern"
        if m is None:
            return ParseError(errmsg)

        # we don't care for matches that aren't immediately in our string
        index = m.start()
        if index != 0:
            return ParseError(errmsg)

        matched = m.group()
        s = s[len(matched):]
        return (matched, s)
    return fn


def array(start: Parser[T], p: Parser[V], end: Parser[K], sep: Parser[S]) -> Parser[list[V]]:
    """a specialised parser for handling array like patterns for example [1,2,3,4] could be parsed by this parser. 
        A call to handle the previous case could look like: array(char('['), integer(), char(']'), char(','))
    """
    def fn(s: str) -> ParseResult[list[V]]:
        maybeStart = start(s)
        if isinstance(maybeStart, ParseError):
            return maybeStart
        (_, s) = maybeStart
        res: list[V] = []
        ignore_sep = True
        while True:
            if ignore_sep:
                ignore_sep = False
            else:
                maybeSep = sep(s)
                if isinstance(maybeSep, ParseError):
                    # maybe we are at the end of the sequence
                    break
                (_, s) = maybeSep

            maybeVal = p(s)
            if isinstance(maybeVal, ParseError):
                break
            (val, s) = maybeVal
            res.append(val)
        maybeEnd = end(s)
        if isinstance(maybeEnd, ParseError):
            return maybeEnd
        (_, s) = maybeEnd
        return (res, s)
    return fn
