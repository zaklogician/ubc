from typing import Mapping, NamedTuple, Reversible, TypeAlias
from logic import find_loop_avoiding
import syntax
from collections.abc import Collection
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

    back_edges: Collection[tuple[str, str]]
    """ edges where the head dominates the tail
        Stored as (tail, head), that is (latch, loop_header)
    """


class BasicNode(NamedTuple):
    upds: tuple[tuple[tuple[str, syntax.Type], syntax.Expr], ...]
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

    name: str

    # TODO: find good way to freeze dict and keep type hints
    nodes: dict[str, CondNode | CallNode | BasicNode]
    """
    Node name to Node
    """

    loops: dict[str, Loop]
    """
    Loop header to loop information
    """

    arguments: tuple[tuple[str, syntax.Type], ...]


def compute_cfg_from_all_succs(all_succs: dict[str, list[str]], entry: str):
    assert is_valid_all_succs(all_succs)
    assert entry in all_succs, f"entry {entry} not in all_succs"

    all_preds = compute_all_predecessors(all_succs)
    assert len(all_preds) == len(all_succs)
    # assert is_valid_all_preds(all_preds)

    all_doms = compute_dominators(
        all_succs=all_succs, all_preds=all_preds, entry=entry)
    return CFG(entry=entry, all_succs=all_succs, all_preds=all_preds, all_doms=all_doms, back_edges=cfg_compute_back_edges(all_succs, all_doms))


def compute_cfg_from_func(func: syntax.Function) -> CFG:
    all_succs = compute_all_successors(func)
    assert func.entry is not None, f"func.entry is None in {func.name}"
    return compute_cfg_from_all_succs(all_succs, func.entry)


def cfg_compute_back_edges(all_succs: dict[str, list[str]], all_doms: dict[str, list[str]]) -> Collection[tuple[str, str]]:
    """ a back edge is an edge who's head dominates their tail
    """

    back_edges: set[tuple[str, str]] = set()
    for n, succs in all_succs.items():
        tail = n
        for head in succs:
            if head in all_doms[tail]:
                back_edges.add((tail, head))
    return frozenset(back_edges)


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
        loop_header: str,
        loop_nodes: tuple[str]) -> tuple[str]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[str] = [loop_header]
    visited = set()

    loop_written_vars: set[str] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, BasicNode):
            for (name, typ), _ in node.upds:
                loop_written_vars.add(name)

        for succ in cfg.all_succs[n]:
            if succ in loop_nodes and (n, succ) not in cfg.back_edges:
                q.append(succ)

    assert len(visited) == len(loop_nodes)

    return tuple(loop_written_vars)


def compute_loops(nodes: dict[str, Node], cfg: CFG) -> dict[str, Loop]:
    """ Map from loop header to Loop
    """
    # compute back edges
    # for each back edge, compute the natural loop
    # for each loop, inspect variables that are written to

    if len(set(loop_header for (t, loop_header) in cfg.back_edges)) < len(cfg.back_edges):

        # We have something like this (ie. multiple loops point use the same header)
        #
        #   -> header <--
        #  /   /     \    \
        # |   /       \    |
        # \   v        v  /
        #   left       right

        raise ValueError(
            "unhandle case: multiple back edges point to the same loop header in function")

    loops: dict[str, Loop] = {}
    # we could do this faster by traversing the entire graph once and keeping
    # track of which loop we are currently in, but this is approach simpler
    # and good enough for now
    for back_edge in cfg.back_edges:
        _, loop_header = back_edge

        loop_nodes = compute_natural_loop(cfg, back_edge)

        assert all(loop_header in cfg.all_doms[n] for n in loop_nodes)

        loop_targets = compute_loop_targets(
            nodes, cfg, loop_header, loop_nodes)
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

    return Function(cfg=cfg, nodes=safe_nodes, loops=loops, arguments=tuple(func.inputs), name=func.name)


def convert_function(func: syntax.Function) -> Function:
    try:
        f = _convert_function(func)
    except Exception as e:
        raise type(e)(f"in function {func.name!r}") from e
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

    visited = set()
    q: list[str] = [n for n, preds in cfg.all_preds.items() if len(preds) == 0]
    while q:
        n = q.pop(0)
        if n in visited:
            continue

        # Visit in topological order, that is, visit all the predecessors first.
        if all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges):
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


Var = tuple[str, syntax.Type]


class Insertion(NamedTuple):
    """ At joint nodes, we need to insert x_n = x_m
    These insertion items keep track of that.
    """

    after: str
    """ Will insert the update after the node 'after' """

    lhs_dsa_name: str
    typ: syntax.Type

    rhs_dsa_value: str


@dataclass
class DSABuilderMutableState:
    k: int
    """ fresh incarnation count
    """

    insertions: list[Insertion]
    """ nodes to insert
    """


def find_latest_incarnation(
        func: Function,
        graph: Mapping[str, Node],
        s: DSABuilderMutableState,
        current_node: str,
        raw_var_name: str,
        typ: syntax.Type,
        skip_current_node=False) -> str:
    preds = func.cfg.all_preds[current_node]
    if len(preds) == 0:
        # is the variable an argument to the function?
        for (dsa_name, typ) in func.arguments:
            name, num = dsa_name.split('.')
            if name == raw_var_name:
                return dsa_name

        # maybe it's a global
        # TODO
        assert False, f"trying to read {raw_var_name} but reached top of the function (is it a global?)"

    # i think skip_current_node == current_node in graph, but i'd just like to make sure
    if not skip_current_node:
        assert current_node in graph, "didn't traverse in topological order"

        node = graph[current_node]
        if isinstance(node, BasicNode):
            for ((dsa_name, typ), _) in node.upds:
                raw, num = dsa_name.split('.')
                if raw == raw_var_name:
                    return dsa_name

        elif isinstance(node, CallNode):
            raise NotImplementedError

    if len(preds) == 1:
        return find_latest_incarnation(func, graph, s, preds[0], raw_var_name, typ)

    latest = [find_latest_incarnation(
        func, graph, s, p, raw_var_name, typ) for p in preds]

    if len(set(latest)) == 1:
        return latest[0]

    # different branch have given different variables
    # TODO: use Leino's optimisation to avoid excessive variables
    s.k = s.k + 1
    fresh_name = raw_var_name + f'.{s.k}'
    for i, pred in enumerate(preds):
        s.insertions.append(
            Insertion(after=pred, lhs_dsa_name=fresh_name,
                      typ=typ, rhs_dsa_value=latest[i])
        )

    return fresh_name


def apply_incarnations(
        func: Function,
        graph: Mapping[str, Node],
        s: DSABuilderMutableState,
        upds: Reversible[tuple[Var, syntax.Expr]],
        current_node: str,
        root: syntax.Expr) -> syntax.Expr:

    # using the Expr.visit is annoying because I need to keep track of state
    # to rebuild the expression
    if root.kind == "Num":
        return root
    elif root.kind == 'Var':
        for ((dsa_name, typ), expr) in reversed(upds):
            assert False, 'should never happen because we never have more than one update per name' \
                          + 'ie. upds is always empty'
            name, num = dsa_name.split('.')
            if root.name == name:
                assert typ == root.typ, f"same name doesn't have same type {dsa_name}"
                return syntax.Expr('Var', root.typ, name=dsa_name)

        # if we don't find it in the current updates, then we look in the parent nodes

        dsa_name = find_latest_incarnation(
            func, graph, s, current_node, root.name, root.typ, skip_current_node=True)
        return syntax.Expr('Var', root.typ, name=dsa_name)

    elif root.kind == 'Op':
        return syntax.Expr('Op', root.typ, name=root.name, vals=[
            apply_incarnations(func, graph, s, upds, current_node, item) for item in root.vals
        ])

    raise NotImplementedError(f"expr.kind={root.kind}")


def apply_insertions(graph: dict[str, Node], insertions: Collection[Insertion]):
    for i, ins in enumerate(insertions):
        assert ins.after in graph, "inserting after an unknown node"
        after = graph[ins.after]
        # if we have a BasicNode, we could technically add an update.
        # However, I don't do this because (1) if the last node is a CallNode,
        # i'll have to insert an extra BasicNode anyway (2) c parser doesn't generate
        # basic nodes with more than one update anyway, so code handling multiple
        # updates either doesn't exists and isn't well tested

        # or we could find the latest basic node before the 'after' node
        # (we are guaranteed to find on the branch because otherwise we would
        # not have had a conflict to resolve in the first place)

        # approach: insert a basic node
        assert not isinstance(
            after, CondNode), "i didn't think this was possible"

        upd: tuple[Var, syntax.Expr] = ((ins.lhs_dsa_name, ins.typ), syntax.Expr(
            'Var', ins.typ, name=ins.rhs_dsa_value))
        joiner = BasicNode((upd, ), succ=after.succ)
        joiner_name = f'j{i}'
        graph[joiner_name] = joiner

        graph[ins.after] = after._replace(succ=joiner_name)


def dsa(func: Function):
    # q = [n for n, preds in func.cfg.all_preds.items() if len(preds) == 0]
    q = [func.cfg.entry]

    visited: set[str] = set()
    graph: dict[str, Node] = {}

    s = DSABuilderMutableState(k=0, insertions=[])

    args = []
    for (arg_name, typ) in func.arguments:
        s.k += 1
        args.append((arg_name + f'.{s.k}', typ))

    # this _replace is documented, but it isn't type safe
    # TOOD: find a way to implement _replace in a type safe way
    func = func._replace(arguments=tuple(args))

    while q:
        # bfs-like topological order so that we visit the longest branches last
        assert visited == set(graph.keys())
        # => means we could get rid of the visited set

        n = q.pop(-1)
        if not all(p in visited for p in func.cfg.all_preds[n]):
            continue

        visited.add(n)

        node = func.nodes[n]
        if isinstance(node, BasicNode):
            upds: list[tuple[Var, syntax.Expr]] = []
            for (var, expr) in node.upds:
                s.k += 1
                varp = (var[0] + f'.{s.k}', var[1])
                exprp = apply_incarnations(func, graph, s, upds, n, expr)
                upds.append((varp, exprp))
            graph[n] = BasicNode(tuple(upds), succ=node.succ)
        elif isinstance(node, CondNode):
            graph[n] = CondNode(
                expr=apply_incarnations(func, graph, s, [], n, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, CallNode):
            raise NotImplementedError

        succs = func.cfg.all_succs[n]
        for succ in succs:
            if (n, succ) not in func.cfg.back_edges:
                q.append(succ)

    apply_insertions(graph, s.insertions)

    return func._replace(nodes=graph)
