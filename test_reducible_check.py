import pytest
from dot_graph import write_successor_graph
from ubc import cfg_is_reducible, compute_cfg_from_all_succs



@pytest.mark.parametrize("all_succs", [
    {"_start": ["if_cond"], "if_cond": ["if_then", "if_else"], "if_then": ["if_join"], "if_else": ["if_join"], "if_join": []},  # diamond
    {
        "_start": ["for_cond"],
        "for_cond": ["for_body", "for_join"],  # loop header
        "for_body": ["for_step"],
        "for_step": ["for_cond"],
        "for_join": [],
    },
    # small infinite loop
    {"_start": ["a"], "a": ["b"], "b": ["a"]},
    # nested loop
    {
        "_start": ["outer_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        "outer_for_body": ["inner_for_cond"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    },
    # sequential loops
    {
        "_start": ["for1_cond"],
        "for1_cond": ["for1_body", "for1_join"],  # loop header
        "for1_body": ["for1_step"],
        "for1_step": ["for1_cond"],
        "for1_join": ["for2_cond"],

        "for2_cond": ["for2_body", "for2_join"],  # loop header
        "for2_body": ["for2_step"],
        "for2_step": ["for2_cond"],
        "for2_join": [],
    },
    # self loop
    {
        "_start": ["loop_header_and_latch"],
        "loop_header_and_latch": ["loop_header_and_latch", "exit"],
        "exit": []
    },
    # single loop break
    # for (; cond1; step) { if (cond2) break; }
    {
        "_start": ["for_cond"],
        "for_cond": ["for_body", "for_join"],
        "for_body": ["for_body_if_cond"],
        "for_body_if_cond": ["for_body_if_then", "for_body_if_join"],
        "for_body_if_then": ["for_join"],
        "for_body_if_join": ["for_step"],
        "for_step": ["for_cond"],
        "for_join": []
    },
    # TODO: continue
    # for (; cond1; step) { if (cond2) continue; }
    {
        "_start": ["for_cond"],
        "for_cond": ["for_body", "for_join"],
        "for_body": ["for_body_if_cond"],
        "for_body_if_cond": ["for_body_if_then", "for_body_if_join"],
        "for_body_if_then": ["for_body_if_join"],
        "for_body_if_join": ["for_step"],
        "for_step": ["for_cond"],
        "for_join": []
    },

    # weird example that still forms one loop!
    {
        "_start": ["for_cond"],
        "for_cond": ["for_body", "for_join"],
        "for_body": ["for_cond"],
        "for_join": ["nasty_jump"],
        "nasty_jump": ["for_body"],
    },

    # inner loop breaks to outer loop body
    {
        "_start": ["outer_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        "outer_for_body": ["inner_for_cond"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_body_if_cond"],
        "inner_for_body_if_cond": ["inner_for_body_if_then", "inner_for_body_if_join"],
        "inner_for_body_if_then": ["inner_for_join"], # break
        "inner_for_body_if_join": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    },

    # inner loop breaks out of both loops
    {
        "_start": ["outer_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        "outer_for_body": ["inner_for_cond"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_body_if_cond"],
        "inner_for_body_if_cond": ["inner_for_body_if_then", "inner_for_body_if_join"],
        "inner_for_body_if_then": ["outer_for_join"], # break
        "inner_for_body_if_join": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    },
])
def test_is_reducible(all_succs):
    assert cfg_is_reducible(compute_cfg_from_all_succs(all_succs, "_start"))

@pytest.mark.parametrize("all_succs", [
    # textbook example
    {
        "_start": ["A", "B"],
        "A": ["B"],
        "B": ["A"],
    },

    # skip loop header
    {
        "_start": ["normal", "skipper"],
        "skipper": ["for_body"],
        "normal": ["for_cond"],
        "for_cond": ["for_body", "for_join"],
        "for_body": ["for_cond"],
        "for_join": []
    },

    # jump between loop bodies (ie skip the second loop header)
    # sequential loops
    {
        "_start": ["for1_cond"],
        "for1_cond": ["for1_body", "for1_join"],  # loop header
        "for1_body": ["for1_step", "for2_body"],
        "for1_step": ["for1_cond"],
        "for1_join": ["for2_cond"],

        "for2_cond": ["for2_body", "for2_join"],  # loop header
        "for2_body": ["for2_step"],
        "for2_step": ["for2_cond"],
        "for2_join": [],
    },

    # jump to header of inner loop from outside both loop
    {
        "_start": ["outer_for_cond", "skipper"],
        "skipper": ["inner_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        "outer_for_body": ["inner_for_cond"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    },

    # skip inner loop header, from outer loop body
    {
        "_start": ["outer_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        # if we just have a jump to the inner for body, it's equivalent to a
        # do while loop
        "outer_for_body": ["inner_for_body", "inner_for_cond"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    },

])
def test_is_not_reducible(all_succs):
    assert not cfg_is_reducible(compute_cfg_from_all_succs(all_succs, "_start"))

if __name__ == "__main__":
    from dot_graph import viz_successor_graph
    viz_successor_graph({
        "_start": ["outer_for_cond"],
        "outer_for_cond": ["outer_for_body", "outer_for_join"],
        "outer_for_body": ["inner_for_body"],

        "inner_for_cond": ["inner_for_body", "inner_for_join"],
        "inner_for_body": ["inner_for_step"],
        "inner_for_step": ["inner_for_cond"],

        "inner_for_join": ["outer_for_step"],
        "outer_for_step": ["outer_for_cond"],
        "outer_for_join": [],
    })
