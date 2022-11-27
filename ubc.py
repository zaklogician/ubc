from typing import Generic, Mapping, NamedTuple, NewType, Reversible, TypeAlias, TypeVar
from logic import find_loop_avoiding
import syntax
from collections.abc import Collection
from dataclasses import dataclass
from functools import reduce
from collections import namedtuple

from typing_extensions import assert_never


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


class EmptyNode(NamedTuple):
    succ: str


ProgVarName = NewType('ProgVarName', str)
DSAVarName = NewType('DSAVarName', str)


def make_dsa_var_name(v: ProgVarName, k: int) -> DSAVarName:
    return DSAVarName(f'{v}.{k}')


def unpack_dsa_var_name(v: DSAVarName) -> tuple[ProgVarName, int]:
    name, num = v.split('.')
    return ProgVarName(name), int(num)


K = TypeVar('K', ProgVarName, DSAVarName)


# TODO: syntax.Expr should know about DSAVarName/ProgVarName

# can't use generics with NamedTuples, the fix is only in python3.11
# and ubuntu comes with python3.10.
# https://github.com/python/cpython/issues/88089
# https://github.com/python/cpython/pull/92027
@dataclass(frozen=True)
class Var(Generic[K]):
    name: K
    typ: syntax.Type


@dataclass(frozen=True)
class Update(Generic[K]):
    var: Var[K]
    expr: syntax.Expr


@dataclass(frozen=True)
class BasicNode(Generic[K]):
    # only support one update per node
    upd: Update[K]
    succ: str


@dataclass(frozen=True)
class CallNode(Generic[K]):
    succ: str
    fname: str
    args: tuple[syntax.Expr]
    rets: tuple[Var[K], ...]


class CondNode(NamedTuple):
    expr: syntax.Expr
    succ_then: str
    succ_else: str


Node = BasicNode[K] | CallNode | CondNode | EmptyNode


class Loop(NamedTuple):
    back_edge: tuple[str, str]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[str, ...]
    """ nodes forming a natural loop """

    targets: Collection[ProgVarName]
    """ All the variables that are written to during the loop
    """

    @property
    def header(self):
        return self.back_edge[1]


@dataclass(frozen=True)
class Function(Generic[K]):

    cfg: CFG

    name: str

    # TODO: find good way to freeze dict and keep type hints
    nodes: Mapping[str, Node[K]]
    """
    Node name => Node
    """

    loops: Mapping[str, Loop]
    """
    loop header => loop information
    """

    arguments: tuple[Var[K], ...]


del K


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
        nodes: dict[str, Node[ProgVarName]],
        cfg: CFG,
        loop_header: str,
        loop_nodes: tuple[str]) -> Collection[ProgVarName]:
    # traverse the loop nodes in topological order
    # (if there is a loop in the body, we ignore its back edge)
    q: list[str] = [loop_header]
    visited = set()

    loop_targets: set[ProgVarName] = set()
    while q:
        n = q.pop(0)
        if not all(p in visited for p in cfg.all_preds[n] if (p, n) not in cfg.back_edges and p in loop_nodes):
            continue
        visited.add(n)

        node = nodes[n]
        if isinstance(node, BasicNode):
            loop_targets.add(node.upd.var.name)
        elif isinstance(node, CallNode):
            raise NotImplementedError
        elif not isinstance(node, EmptyNode | CondNode):
            assert_never(node)

        for succ in cfg.all_succs[n]:
            if succ in loop_nodes and (n, succ) not in cfg.back_edges:
                q.append(succ)

    assert len(visited) == len(loop_nodes)
    return loop_targets


def compute_loops(nodes: dict[str, Node[ProgVarName]], cfg: CFG) -> dict[str, Loop]:
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
            if len(node.upds) == 0:
                safe_nodes[name] = EmptyNode(succ=node.cont)
            else:
                assert len(node.upds) == 1
                var = Var(ProgVarName(node.upds[0][0][0]), node.upds[0][0][1])
                upd = Update(var=var, expr=node.upds[0][1])
                safe_nodes[name] = BasicNode(upd=upd, succ=node.cont)
        elif node.kind == "Call":
            safe_nodes[name] = CallNode(
                succ=node.cont, fname=node.fname, args=tuple(node.args), rets=tuple(Var(ProgVarName(name), typ) for name, typ in node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = CondNode(
                succ_then=node.left, succ_else=node.right, expr=node.cond)
        else:
            raise ValueError(f"unknown kind {node.kind!r}")

    loops = compute_loops(safe_nodes, cfg)

    args = tuple(Var(ProgVarName(name), typ) for name, typ in func.inputs)

    return Function(cfg=cfg, nodes=safe_nodes, loops=loops, arguments=args, name=func.name)


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
    # have we visited all the nodes? Not possible if there's a cycle, because
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


class Insertion(NamedTuple):
    """ At joint nodes, we need to insert x_n = x_m
    These insertion items keep track of that.
    """

    after: str
    """ Will insert the update after the node 'after' """

    lhs_dsa_name: DSAVarName
    typ: syntax.Type

    rhs_dsa_value: DSAVarName


@dataclass
class DSABuilderMutableState:
    k: int
    """ Fresh incarnation count

    To allocate a new variable:

        s.k += 1
        make_dsa_var_name(base_name, s.k)

    Mutable during construction
    """

    insertions: list[Insertion]
    """ Nodes to insert (join nodes)

    Mutable during construction
    """

    # TODO: use different types for raw var name and dsa var names
    loop_targets_incarnations: Mapping[str, dict[ProgVarName, DSAVarName]]
    """
    Loop header => prog_var_name => dsa_var_name

    (Recall that a loop header uniquely identifies a loop)

    When we read a variable from a block, we go up the CFG to find where it
    was defined. If we stumble upon a loop header, and this loop writes to
    that specific variable (ie this variable is a loop target), then we must
    not continue looking up the graph! That variable must be havoced.

    That is, the first time you lookup a loop target in the loop header, you
    return a fresh variable f. Later on, if more blocks ask for that same
    variable, we must return the same f.

    This mapping keeps track of which loop targets have been incarnated so far.

    Mutable during construction
    """

    func_args: tuple[Var[DSAVarName], ...]
    """ The function's arguments in with DSA numbers associated to the
        arguments
    """


def find_latest_incarnation(
        func: Function[ProgVarName],
        dsa_nodes: Mapping[str, Node[DSAVarName]],
        s: DSABuilderMutableState,
        current_node: str,
        prog_var_name: ProgVarName,
        typ: syntax.Type,
        skip_current_node=False) -> DSAVarName:

    # see loop_targets_incarnations' comment
    if current_node in func.loops and prog_var_name in func.loops[current_node].targets:

        if prog_var_name not in s.loop_targets_incarnations[current_node]:
            s.k += 1
            s.loop_targets_incarnations[current_node][prog_var_name] = make_dsa_var_name(
                prog_var_name, s.k)

        return s.loop_targets_incarnations[current_node][prog_var_name]

    # i think skip_current_node == current_node in dsa_nodes, but i'd just like to make sure
    if not skip_current_node:
        assert current_node in dsa_nodes, f"didn't traverse in topological order {current_node=}"

        node = dsa_nodes[current_node]
        if isinstance(node, BasicNode):
            name, num = unpack_dsa_var_name(node.upd.var.name)
            if prog_var_name == name:
                return node.upd.var.name
        elif isinstance(node, CallNode):
            raise NotImplementedError
        # otherwise, keep looking up the graph

    # don't go searching up back edges
    preds = [p for p in func.cfg.all_preds[current_node]
             if (p, current_node) not in func.cfg.back_edges]

    if len(preds) == 0:
        # is the variable an argument to the function?
        for arg in s.func_args:
            name, num = unpack_dsa_var_name(arg.name)
            if name == prog_var_name:
                return arg.name

        # maybe it's a global
        # TODO
        assert False, f"trying to read {prog_var_name} but reached top of the function (is it a global?)"

    if len(preds) == 1:
        return find_latest_incarnation(func, dsa_nodes, s, preds[0], prog_var_name, typ)

    latest = [find_latest_incarnation(
        func, dsa_nodes, s, p, prog_var_name, typ) for p in preds]

    if len(set(latest)) == 1:
        return latest[0]

    # different branch have given different variables
    # TODO: use Leino's optimisation to avoid excessive variables
    s.k = s.k + 1
    fresh_name = DSAVarName(prog_var_name + f'.{s.k}')
    for i, pred in enumerate(preds):
        s.insertions.append(
            Insertion(after=pred, lhs_dsa_name=fresh_name,
                      typ=typ, rhs_dsa_value=latest[i])
        )

    return fresh_name


def apply_incarnations(
        func: Function[ProgVarName],
        graph: Mapping[str, Node],
        s: DSABuilderMutableState,
        current_node: str,
        root: syntax.Expr) -> syntax.Expr:

    # using the Expr.visit is annoying because I need to keep track of state
    # to rebuild the expression
    if root.kind == "Num":
        return root
    elif root.kind == 'Var':
        dsa_name = find_latest_incarnation(
            func, graph, s, current_node, root.name, root.typ, skip_current_node=True)
        return syntax.Expr('Var', root.typ, name=dsa_name)

    elif root.kind == 'Op':
        return syntax.Expr('Op', root.typ, name=root.name, vals=[
            apply_incarnations(func, graph, s, current_node, item) for item in root.vals
        ])

    raise NotImplementedError(f"expr.kind={root.kind}")


def apply_insertions(graph: dict[str, Node[DSAVarName]], insertions: Collection[Insertion]):
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

        var = Var(DSAVarName(ins.lhs_dsa_name), ins.typ)
        expr = syntax.Expr('Var', ins.typ, name=ins.rhs_dsa_value)
        joiner = BasicNode(Update(var, expr), succ=after.succ)
        joiner_name = f'j{i}'
        graph[joiner_name] = joiner

        graph[ins.after] = dataclass.replace(after, succ=joiner_name)


def dsa(func: Function[ProgVarName]) -> Function[DSAVarName]:
    # q = [n for n, preds in func.cfg.all_preds.items() if len(preds) == 0]
    q = [func.cfg.entry]

    dsa_nodes: dict[str, Node[DSAVarName]] = {}
    visited: set[str] = set()

    # this is hack to deal with the weird assert False() node
    for n, preds in func.cfg.all_preds.items():
        if len(preds) == 0 and n != func.cfg.entry:
            # assert len(expr_variables(func.nodes[n])) == 0  # TODO
            node = func.nodes[n]
            assert isinstance(node, CondNode) and node.expr == syntax.Expr(
                'Op', syntax.Type('Builtin', 'Bool'), name='False', vals=[])
            dsa_nodes[n] = node
            visited.add(n)

    k = 0
    dsa_args: list[Var[DSAVarName]] = []
    for arg in func.arguments:
        k += 1
        dsa_args.append(Var(make_dsa_var_name(arg.name, k), arg.typ))

    s = DSABuilderMutableState(k=k, insertions=[], loop_targets_incarnations={
                               loop_header: {} for loop_header in func.loops},
                               func_args=tuple(dsa_args))

    while q:
        # bfs-like topological order so that we visit the longest branches last
        n = q.pop(-1)
        if n == 'Err' or n == 'Ret':
            visited.add(n)
            continue

        # (if n in dsa_nodes.keys(), that means that n was visited)
        # visit in topolocial order ignoring back edges
        if not all(p in visited for p in func.cfg.all_preds[n] if (p, n) not in func.cfg.back_edges):
            continue

        visited.add(n)

        node = func.nodes[n]
        if isinstance(node, BasicNode):
            upds: list[tuple[Var, syntax.Expr]] = []
            s.k += 1
            varp = Var(make_dsa_var_name(
                node.upd.var.name, s.k), node.upd.var.typ)
            exprp = apply_incarnations(func, dsa_nodes, s, n, node.upd.expr)
            dsa_nodes[n] = BasicNode(Update(varp, exprp), succ=node.succ)
        elif isinstance(node, CondNode):
            dsa_nodes[n] = CondNode(
                expr=apply_incarnations(func, dsa_nodes, s, n, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, CallNode):
            raise NotImplementedError
        elif isinstance(node, EmptyNode):
            dsa_nodes[n] = node
        else:
            assert assert_never(node)

        succs = func.cfg.all_succs[n]
        for succ in succs:
            if (n, succ) not in func.cfg.back_edges:
                q.append(succ)

    apply_insertions(dsa_nodes, s.insertions)

    assert len(visited) == num_reachable(
        func.cfg), f"{visited} {len(visited)} {num_reachable(func.cfg)} {func.name}"

    return Function[DSAVarName](
        cfg=func.cfg,
        arguments=tuple(dsa_args),
        loops=func.loops,
        name=func.name,
        nodes=dsa_nodes)
