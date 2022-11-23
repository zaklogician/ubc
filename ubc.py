import syntax
from collections.abc import Container
from dataclasses import dataclass
from functools import reduce


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

    doms[entry] = set([entry])
    assert all_succs.keys() == all_preds.keys()
    for n in all_succs:
        if n != entry:
            doms[n] = set(all_succs.keys())

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


@dataclass()
class CFG:
    """
    Class that groups information about a function's control flow graph
    """

    entry: str

    all_succs: dict[str, list[str]]
    """ Successors """

    all_preds: dict[str, list[str]]
    """ Predecessors """

    all_doms: dict[str, list[str]]
    """ Dominators """


@dataclass()
class Function:

    cfg: CFG

    # TODO: use namedtuples
    nodes: dict[str, syntax.Node]


# even though it might be less efficient, we run both of these
# transformations (on func.nodes) before generating the predecessors and
# successors graph so that we don't have to patch them all.
#
# we edit *only* the func.nodes, and then derive all the other graphs from
# there.

def remove_contradiction_entry_node(func: syntax.Function):
    """ for some reason, there often is a Cond False() ? Err : x node that
    doesn't have any predecessors

    It's not even to ensure that the Err blocks has a predecessor
    (see Kernel_C.alignUp)

    it's a pain for some the analysis (a function should only have one entry
    point), so we remove it.
    """

    contr_entry = None
    for n, node in func.nodes.items():
        if node.kind == 'Cond' and node.right == 'Err' and func.nodes[node.left].kind == "Basic" and func.nodes[node.left].cont == 'Ret' and node.cond == syntax.Expr('Op', syntax.Type('Builtin', 'Bool'), name='False', vals=[]):
            contr_entry = n

    if contr_entry:
        del func.nodes[contr_entry]
    assert 'Err' not in func.nodes


def is_assert_true_node(n): return n.kind == 'Cond' \
    and n.cond == syntax.Expr('Op', syntax.Type('Builtin', 'Bool'), name='True', vals=[]) \
    and n.right == 'Err'


def _remove_assert_true_node(nodes: dict[str, syntax.Node], target: str):
    # 1. find all the predecessors of name
    # 2. rewire them all the current node's successor
    assert is_assert_true_node(nodes[target])

    preds: list[syntax.Node] = []
    for n, node in nodes.items():
        if target in node.get_conts():
            preds.append(node)

    succ = nodes[target].left
    assert succ != 'Err'
    for pred in preds:
        # todo: please use inheritance :(
        if pred.kind == 'Call' or pred.kind == 'Basic':
            pred.cont = succ
        elif pred.kind == 'Cond':
            if pred.left == target:
                pred.left = succ
            elif pred.right == target:
                pred.right = succ


def remove_assert_true_nodes(func: syntax.Function):
    """ There are some `assert True` nodes inserted in the graphs
        for some reason. Sometimes, they mess up the domination relations
        and turn a reducible CFG into an irreducible one.

        Here's an example: TODO
    """

    nodes_to_remove: list[str] = []

    for n, node in func.nodes.items():
        if is_assert_true_node(node):
            # 1. find all the predecessors
            # 2. rewire them all the current node's successor
            nodes_to_remove.append(n)

    for n in nodes_to_remove:
        _remove_assert_true_node(func.nodes, n)


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


def num_reachable(cfg: CFG) -> int:
    q: list[str] = [cfg.entry]
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

    # a back edge is an edge who's head dominates their tail
    back_edges: set[tuple[str, str]] = set()
    for n, succs in cfg.all_succs.items():
        tail = n
        for head in succs:
            if head in cfg.all_doms[tail]:
                back_edges.add((tail, head))

    visited = set()
    q: list[str] = [cfg.entry]
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
