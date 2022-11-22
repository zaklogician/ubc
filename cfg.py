""" Control Flow Graph representation
"""

from typing import List, Tuple
import syntax


class Node:
    def __init__(self):
        self.predecessors = []  # type: List[Node]
        self.dominators = []  # type: List[Node]

        # will have
        # self.bicondition


class NodeBasic(Node):
    def __init__(self, succ, upds):
        super().__init__()
        self.successor = succ  # type: Node
        self.upds = upds  # type: List[Tuple[Tuple[str, syntax.Type], syntax.Expr]]


class NodeCall(Node):
    def __init__(self, succ, fname, args, rets):
        self.successor = succ  # type: Node
        self.fname = fname  # type: str
        self.args = args  # type: List[syntax.Expr]
        self.rets = rets  # type: List[Tuple[str, syntax.Type]]


class NodeCond(Node):
    def __init__(self, succ_left, succ_right, cond):
        self.successor_left = succ_left  # type: Node
        self.successor_right = succ_right  # type: Node
        self.cond = cond  # type: syntax.Expr


def convert_graphlang_to_cfg(graphlang):
    # type: (syntax.Node) -> Node
    pass


def compute_cfg(graphlang):
    # type: (syntax.Node) -> Node
    cfg = convert_graphlang_to_cfg(graphlang)
    compute_predecessors(cfg)
    compute_dominators(cfg)
    return cfg
