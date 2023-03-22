import sys
import enum
from typing_extensions import assert_never


class State(enum.Enum):
    FRESH = 'FRESH'
    EXPECTING_SAT = 'EXPECTING_SAT'
    EXPECTING_UNSAT = 'EXPECTING_UNSAT'


s = State.FRESH


def check(s: State, i: int, line: str) -> State:
    if s is State.FRESH:
        if line == '"should be sat"':
            return State.EXPECTING_SAT
        elif line == '"should be unsat"':
            return State.EXPECTING_UNSAT
        else:
            raise ValueError(f"unknown content on line {i}, {line!r}")
    elif s is State.EXPECTING_SAT:
        if line == "sat":
            return State.FRESH
        if line == "unsat":
            raise ValueError("got 'unsat' but expected 'sat'")
        raise ValueError(f"unexpected content on line {i}, {line!r}")
    elif s is State.EXPECTING_UNSAT:
        if line == "unsat":
            return State.FRESH
        if line == "sat":
            raise ValueError("got 'sat' but expected 'unsat'")
        raise ValueError(f"unexpected content on line {i}, {line!r}")
    else:
        assert_never(s)


num_lines = 0
for i, line in enumerate(sys.stdin):
    s = check(s, i, line.strip())
    num_lines += 1
print(f'{num_lines // 2} tests passed')
