import syntax
import logic
from typing import Dict, List, Set, Iterable


def sets_intersection(sets):
    # type: (Iterable[Set]) -> Set
    try:
        inte = next(sets)
    except StopIteration:
        return set([])

    for s in sets:
        inte = inte.intersection(s)
    return inte


# There exists more efficient algorithms, but we can implement them if this
# becomes a bottle next
def compute_dominators(entry, nodes, preds):
    # type: (str, Dict[str, syntax.Node], Dict[str, List[str]]) -> Dict[str, List[str]]

    doms = {}  # type: Dict[str, Set[str]]
    doms[entry] = set([entry])
    for name in nodes:
        if name != entry:
            doms[name] = set(nodes.keys())

    changed = True
    while changed:
        changed = False
        for name in nodes:
            if name == entry:
                continue
            new_doms = set([name]).union(
                sets_intersection(doms[p] for p in preds[name])
            )
            if new_doms != doms[name]:
                changed = True
            doms[name] = new_doms

    return {name: list(sorted(doms[name])) for name in doms}


def undefined_behaviour_c(graph_file, function_name):
    with open(graph_file) as f:
        struct, functions, const_globals = syntax.parse_and_install_all(f, None)

    function = functions[function_name]
    preds = logic.compute_preds(function.nodes)
    doms = compute_dominators(function.entry, function.nodes, preds)
    print(doms)
    while True:
        name = input("name: ")
        if name in doms:
            print(doms[name])
        else:
            print("name not found in", list(doms.keys()))
