from __future__ import annotations
import os
import tempfile
from contextlib import contextmanager
from typing import Iterator, TypeVar


def clen(it: Iterator) -> int:
    """ returns the number of elemens in the iterator, even if that means it has to consume it
    """
    return sum(1 for _ in it)


K = TypeVar("K")


def set_intersection(it: Iterator[set[K]]) -> set[K]:
    # intersection of no set is the universal set. We don't know what that is,
    # so if it doesn't generate at least one element, we let next raise the
    # error
    acc: set[K] = next(it)
    for s in it:
        acc = acc.intersection(s)
    return acc


def set_union(it: Iterator[set[K]]) -> set[K]:
    try:
        acc = next(it)
    except StopIteration:
        return set()  # union of no set is the empty set
    for s in it:
        acc = acc.union(s)
    return acc


@contextmanager
def open_temp_file(suffix: str | None = None, prefix: str | None = None, dir: str | None = None, text: bool = False):
    fd, name = tempfile.mkstemp(
        suffix=suffix, prefix=prefix, dir=dir, text=text)
    try:
        yield os.fdopen(fd, 'w'), name
    finally:
        os.remove(name)
