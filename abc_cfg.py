from typing_extensions import assert_never
from source import ExprVar, Loop, LoopHeaderName, NodeBasic, NodeCall, NodeCond, NodeEmpty, NodeName, NodeNameErr, NodeNameRet, ProgVarName, VarNameKind, convert_function_nodes, Node
from typing import Collection, Mapping, NamedTuple, Sequence

from utils import clen


class CFG(NamedTuple):
    """
    Class that groups information about a function's control flow graph
    """

    entry: NodeName
    # TODO: make those lists a tuple/Collection/Sequence/Set?
    all_succs: Mapping[NodeName, Sequence[NodeName]]
    """ Successors """

    all_preds: Mapping[NodeName, Sequence[NodeName]]
    """ Predecessors """

    all_doms: Mapping[NodeName, Sequence[NodeName]]
    """ Dominators of key (a in all_doms[b] means a dominates b) """

    back_edges: Collection[tuple[NodeName, NodeName]]
    """ edges where the head dominates the tail
        Stored as (tail, head), that is (latch, loop_header)
    """


def compute_all_successors_from_nodes(nodes: Mapping[NodeName, Node]) -> Mapping[NodeName, list[NodeName]]:
    all_succs: dict[NodeName, list[NodeName]] = {}
    for name, node in nodes.items():
        all_succs[name] = []
        if isinstance(node, NodeBasic | NodeCall | NodeEmpty):
            all_succs[name].append(node.succ)
        elif isinstance(node, NodeCond):
            all_succs[name].append(node.succ_then)
            all_succs[name].append(node.succ_else)
        else:
            assert_never(node)

    # if there is at least one node jumping to Err (ie. at least one assert)
    # we add it
    for succs in all_succs.values():
        if NodeNameErr in succs:
            assert NodeNameErr not in all_succs
            all_succs[NodeNameErr] = []
            break

    assert any(NodeNameRet in succs for succs in all_succs.values()
               ), "I assumed at least one node should jump to NodeNameRet"

    assert NodeNameRet not in all_succs
    all_succs[NodeNameRet] = []

    return all_succs


def compute_all_predecessors(all_succs: Mapping[NodeName, list[NodeName]]) -> Mapping[NodeName, list[NodeName]]:
    g: Mapping[NodeName, list[NodeName]] = {n: [] for n in all_succs}
    for n, succs in all_succs.items():
        for succ in succs:
            g[succ].append(n)
    return g

# algorithm from https://en.wikipedia.org/wiki/Dominator_(graph_theory) there
# exists more efficient algorithms, but we can implement them if it turns out
# this is a bottle neck


def compute_dominators(all_succs: Mapping[NodeName, list[NodeName]], all_preds: Mapping[NodeName, list[NodeName]], entry: NodeName) -> Mapping[NodeName, list[NodeName]]:
    # all the nodes that dominate the given node
    doms: dict[NodeName, set[NodeName]] = {}
    for n, preds in all_preds.items():
        if len(preds) == 0:
            doms[n] = set([n])
        else:
            doms[n] = set(all_preds.keys())

    changed = True
    while changed:
        changed = False

        for n in all_succs.keys():
            npreds = all_preds[n]
            if not npreds:
                continue

            new_dom = doms[next(iter(npreds))].intersection(
                *(doms[p] for p in npreds))
            new_dom.add(n)

            if new_dom != doms[n]:
                changed = True
                doms[n] = new_dom

    return {n: list(doms[n]) for n in doms.keys()}


def compute_cfg_from_all_succs(all_succs: Mapping[NodeName, list[NodeName]], entry: NodeName) -> CFG:
    assert_valid_all_succs(all_succs)
    assert entry in all_succs, f"entry {entry} not in all_succs"

    all_preds = compute_all_predecessors(all_succs)
    assert len(all_preds) == len(all_succs)
    # assert is_valid_all_preds(all_preds)

    all_doms = compute_dominators(
        all_succs=all_succs, all_preds=all_preds, entry=entry)
    return CFG(entry=entry, all_succs=all_succs, all_preds=all_preds, all_doms=all_doms, back_edges=cfg_compute_back_edges(all_succs, all_doms))


def cfg_compute_back_edges(all_succs: Mapping[NodeName, list[NodeName]], all_doms: Mapping[NodeName, list[NodeName]]) -> Collection[tuple[NodeName, NodeName]]:
    """ a back edge is an edge who's head dominates their tail
    """

    back_edges: set[tuple[NodeName, NodeName]] = set()
    for n, succs in all_succs.items():
        tail = n
        for head in succs:
            if head in all_doms[tail]:
                back_edges.add((tail, head))
    return frozenset(back_edges)


def compute_natural_loop(cfg: CFG, back_edge: tuple[NodeName, NodeName]) -> tuple[NodeName, ...]:
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
        nodes: Mapping[NodeName, Node[VarNameKind]],
        cfg: CFG,
        loop_header: NodeName,
        loop_nodes: tuple[NodeName, ...]) -> Collection[ExprVar[VarNameKind]]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[NodeName] = [loop_header]
    visited = set()

    loop_targets: set[ExprVar[VarNameKind]] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, NodeBasic):
            for upd in node.upds:
                loop_targets.add(upd.var)
        elif isinstance(node, NodeCall):
            for ret in node.rets:
                loop_targets.add(ret)
        elif not isinstance(node, NodeEmpty | NodeCond):
            assert_never(node)

        for succ in cfg.all_succs[n]:
            if succ in loop_nodes and (n, succ) not in cfg.back_edges:
                q.append(succ)

    assert len(visited) == len(loop_nodes)
    return loop_targets


def assert_single_loop_header_per_loop(cfg: CFG):
    # This assert protects against this:
    #
    #   -> header <--
    #  /   /     \    \
    # |   /       \    |
    #  \  v        v  /
    #   left       right
    assert len(set(loop_header for (t, loop_header) in cfg.back_edges)) == len(cfg.back_edges), \
        "unhandle case: multiple back edges point to the same loop header in function"


def compute_loops(nodes: Mapping[NodeName, Node[ProgVarName]], cfg: CFG) -> Mapping[LoopHeaderName, Loop[ProgVarName]]:
    """ Map from loop header to Loop
    """
    assert_single_loop_header_per_loop(cfg)

    loops: dict[LoopHeaderName, Loop[ProgVarName]] = {}
    # we could do this faster by traversing the entire graph once and keeping
    # track of which loop we are currently in, but this is approach simpler
    # and good enough for now
    for back_edge in cfg.back_edges:
        _, loop_header = back_edge

        loop_nodes = compute_natural_loop(cfg, back_edge)

        assert all(loop_header in cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        loop_targets = compute_loop_targets(
            nodes, cfg, loop_header, loop_nodes)
        loops[LoopHeaderName(loop_header)] = Loop(
            back_edge, loop_nodes, loop_targets)
    return loops


def compute_all_nodes(all_succs: Mapping[NodeName, Sequence[NodeName]]):
    all_nodes: set[NodeName] = set(all_succs.keys())
    for n, succs in all_succs.items():
        all_nodes.update(succs)
    return all_nodes


def is_reducible(cfg: CFG):
    # use definition of reducibility from Aho, Sethi and Ullman 1986 p.606
    #
    # 1. the forward edges form an acyclic graph in which every node can be
    #    reach from the entry
    # 2. the back edges consists only of edges whose head dominates their tail
    #    (tail --> head)

    # updated!

    visited = set()
    q: list[NodeName] = [n for n, preds in cfg.all_preds.items()
                         if clen(p for p in preds if (n, p) not in cfg.back_edges) == 0]
    while q:
        n = q.pop(0)
        if n in visited:
            continue

        # Visit in topological order, that is, visit all the predecessors first.
        if all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges):
            visited.add(n)
            q += cfg.all_succs[n]

    # have we visited all the nodes? Not possible if there's a cycle, because
    # there would always be a predecessor who hadn't been visited yet
    return visited == compute_all_nodes(cfg.all_succs)


def assert_valid_all_succs(all_succs: Mapping[NodeName, list[NodeName]]):
    # entry node should be a key of all_succs, even if they don't have any
    # successors
    for n, succs in all_succs.items():
        for succ in succs:
            assert succ in all_succs, f"{succ=} {all_succs.keys()=}"
