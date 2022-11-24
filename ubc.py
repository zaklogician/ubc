from typing import NamedTuple, TypeAlias
import syntax
from collections.abc import Container
from dataclasses import dataclass
from functools import reduce
from collections import namedtuple


def compute_all_successors(function: syntax.Function) -> dict[str, list[str]]:
    all_succs = {}
    for name, node in function.nodes.items():
        all_succs[name] = []
        for cont in node.get_conts():
            all_succs[name].append(cont)

    assert 'Err' not in all_succs
    all_succs['Err'] = []

    assert 'Ret' not in all_succs
    all_succs['Ret'] = []
    return all_succs


def compute_all_predecessors(all_succs: dict[str, list[str]]) -> dict[str, list[str]]:
    g = {n: [] for n in all_succs}
    for n, succs in all_succs.items():
        for succ in succs:
            g[succ].append(n)
    return g

# algorithm from https://en.wikipedia.org/wiki/Dominator_(graph_theory) there
# exists more efficient algorithms, but we can implement them if it turns out
# this is a bottle neck


def compute_dominators(all_succs: dict[str, list[str]], all_preds: dict[str, list[str]], entry: str) -> dict[str, list[str]]:
    # all the nodes that dominate the given node
    doms: dict[str, set[str]] = {}
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
            new_dom = set([n]) | reduce(set.intersection,
                                        (doms[p] for p in npreds), doms[npreds[0]])
            if new_dom != doms[n]:
                changed = True
                doms[n] = new_dom

    return {n: list(doms[n]) for n in doms.keys()}


# TODO: convert lists to tuples
class CFG(NamedTuple):
    """
    Class that groups information about a function's control flow graph
    """

    entry: str

    all_succs: dict[str, list[str]]
    """ Successors """

    all_preds: dict[str, list[str]]
    """ Predecessors """

    all_doms: dict[str, list[str]]
    """ Dominators of key (a in all_doms[b] means a dominates b) """


class BasicNode(NamedTuple):
    upds: tuple[tuple[tuple[str, syntax.Type], syntax.Expr]]
    succ: str


class CallNode(NamedTuple):
    succ: str
    fname: str
    args: tuple[syntax.Expr]
    rets: tuple[tuple[str, syntax.Type]]


class CondNode(NamedTuple):
    expr: syntax.Expr
    succ_then: str
    succ_else: str


Node = BasicNode | CallNode | CondNode


class Loop(NamedTuple):
    back_edge: tuple[str, str]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[str, ...]
    """ nodes forming a natural loop """

    targets: tuple[str, ...]
    """ All the variables that are written to during the loop
    """


class Function(NamedTuple):

    cfg: CFG

    # TODO: find good way to freeze dict and keep type hints
    nodes: dict[str, CondNode | CallNode | BasicNode]
    """
    Node name to Node
    """

    loops: dict[str, Loop]
    """
    Loop header to loop information
    """


def compute_cfg_from_all_succs(all_succs: dict[str, list[str]], entry: str):
    assert is_valid_all_succs(all_succs)
    assert entry in all_succs, f"entry {entry} not in all_succs"

    all_preds = compute_all_predecessors(all_succs)
    assert len(all_preds) == len(all_succs)
    # assert is_valid_all_preds(all_preds)

    all_doms = compute_dominators(
        all_succs=all_succs, all_preds=all_preds, entry=entry)
    return CFG(entry=entry, all_succs=all_succs, all_preds=all_preds, all_doms=all_doms)


def compute_cfg_from_func(func: syntax.Function) -> CFG:
    all_succs = compute_all_successors(func)
    assert func.entry is not None, f"func.entry is None in {func.name}"
    return compute_cfg_from_all_succs(all_succs, func.entry)


def cfg_compute_back_edges(cfg: CFG):
    """ a back edge is an edge who's head dominates their tail
    """

    back_edges: set[tuple[str, str]] = set()
    for n, succs in cfg.all_succs.items():
        tail = n
        for head in succs:
            if head in cfg.all_doms[tail]:
                back_edges.add((tail, head))
    return back_edges


def compute_natural_loop(cfg: CFG, back_edge: tuple[str, str]) -> tuple[str, ...]:
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
        nodes: dict[str, Node],
        cfg: CFG,
        back_edges: set[tuple[str, str]],
        loop_header: str,
        loop_nodes: tuple[str]) -> tuple[str]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[str] = [loop_header]
    visited = set()

    loop_written_vars: set[str] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, BasicNode):
            for (name, typ), _ in node.upds:
                loop_written_vars.add(name)

        for succ in cfg.all_succs[n]:
            if succ in loop_nodes and (n, succ) not in back_edges:
                q.append(succ)

    assert len(visited) == len(loop_nodes)

    return tuple(loop_written_vars)


def compute_loops(nodes: dict[str, Node], cfg: CFG) -> dict[str, Loop]:
    """ Map from loop header to Loop
    """
    # compute back edges
    # for each back edge, compute the natural loop
    # for each loop, inspect variables that are written to

    # loop header -> all loop nodes
    back_edges = cfg_compute_back_edges(cfg)

    if len(set(loop_header for (t, loop_header) in back_edges)) < len(back_edges):
        """
        We have something like this (ie. multiple loops point use the same header)

          -> header <--
         /   /     \    \
        |   /       \    |
        \   v        v  /
          left       right
        """
        raise ValueError(
            "unhandle case: multiple back edges point to the same loop header in function")

    loops: dict[str, Loop] = {}
    # we could do this faster by traversing the entire graph once and keeping
    # track of which loop we are currently in, but this is approach simpler
    # and good enough for now
    for back_edge in back_edges:
        _, loop_header = back_edge

        loop_nodes = compute_natural_loop(cfg, back_edge)

        assert all(loop_header in cfg.all_doms[n] for n in loop_nodes)

        loop_targets = compute_loop_targets(
            nodes, cfg, back_edges, loop_header, loop_nodes)
        loops[loop_header] = Loop(back_edge, loop_nodes, loop_targets)
    return loops


def _convert_function(func: syntax.Function) -> Function:
    cfg = compute_cfg_from_func(func)
    safe_nodes = {}
    for name, node in func.nodes.items():
        if node.kind == "Basic":
            safe_nodes[name] = BasicNode(upds=tuple(node.upds), succ=node.cont)
        elif node.kind == "Call":
            safe_nodes[name] = CallNode(
                succ=node.cont, fname=node.fname, args=tuple(node.args), rets=tuple(node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = CondNode(
                succ_then=node.left, succ_else=node.right, expr=node.cond)
        else:
            raise ValueError(f"unknown kind {node.kind!r}")

    loops = compute_loops(safe_nodes, cfg)

    return Function(cfg, safe_nodes, loops)


def convert_function(func: syntax.Function) -> Function:
    try:
        f = _convert_function(func)
    except Exception as e:
        raise type(e)(f"in function {func.name!r}") from e
        raise
    return f


def num_reachable(cfg: CFG) -> int:
    q: list[str] = [n for n, preds in cfg.all_preds.items() if len(preds) == 0]
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

    back_edges = cfg_compute_back_edges(cfg)

    visited = set()
    q: list[str] = [n for n, preds in cfg.all_preds.items() if len(preds) == 0]
    while q:
        n = q.pop(0)
        if n in visited:
            continue

        # Visit in topological order, that is, visit all the predecessors first.
        if all(p in visited for p in cfg.all_preds[n] if (p, n) not in back_edges):
            visited.add(n)
            q += cfg.all_succs[n]
    # have we visited all the nodes? Not possible is there's a cycle, because
    # there would always be a predecessor who hadn't been visited yet
    return len(visited) == num_reachable(cfg)


def is_valid_all_succs(all_succs: dict[str, list[str]]) -> bool:
    # entry node should be a key of all_succs, even if they don't have any
    # successors
    for n, succs in all_succs.items():
        for succ in succs:
            if succ not in all_succs:
                return False
    return True


def is_valid_all_preds(all_preds: dict[str, list[str]]) -> bool:
    # there should only ever be one entry point, that is one node with no predecessors
    num_entries = 0
    for n, preds in all_preds.items():
        if len(preds) == 0:
            num_entries += 1
        if num_entries >= 2:
            return False
    return True
