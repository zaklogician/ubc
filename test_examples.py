import pytest
import source
import dsa
import assume_prove
import smt
import syntax

# global variables are bad :(
syntax.set_arch('rv64')


with open('examples/kernel_CFunctions.txt') as f:
    kernel_CFunctions = syntax.parse_and_install_all(f, None)

with open('tests/all.txt') as f:
    test_CFunctions = syntax.parse_and_install_all(f, None)

with open('examples/dsa.txt') as f:
    example_dsa_CFunctions = syntax.parse_and_install_all(f, None)
del f


def verify(unsafe_func: syntax.Function) -> smt.VerificationResult:
    prog_func = source.convert_function(unsafe_func)
    dsa_func, dsa_contexts = dsa.dsa(prog_func)
    prog = assume_prove.make_prog(dsa_func, dsa_contexts)
    smtlib = smt.make_smtlib(prog)
    sats = tuple(smt.send_smtlib_to_z3(smtlib))
    return smt.parse_sats(sats)


@pytest.mark.parametrize('func_name, expected', (
    ("simple", smt.VerificationResult.FAIL),
    ("two_vars", smt.VerificationResult.FAIL),
    ("if_join", smt.VerificationResult.OK),
    ("if_join_different_length", smt.VerificationResult.OK),
    ("if_join_multiple_variables", smt.VerificationResult.OK),
    ("if_join_multiple_variables_no_ret", smt.VerificationResult.OK),
    ("elif_chain", smt.VerificationResult.OK),
    ("simple_for_loop", smt.VerificationResult.FAIL),
    ("shift_diag", smt.VerificationResult.FAIL),
    ("fail_one_branch_undefined", smt.VerificationResult.FAIL),
    ("one_branch_legal", smt.VerificationResult.OK),
    ("fail_uninit", smt.VerificationResult.OK),
    ("init", smt.VerificationResult.OK),
    ("fail_arr_undefined_behaviour", smt.VerificationResult.FAIL),
    ("fail_zoltans_horrible_fail_arr_undefined_behaviour", smt.VerificationResult.FAIL),
    ("fail_arr_undefined_behaviour2", smt.VerificationResult.FAIL),
    ("arr_static", smt.VerificationResult.OK),
    # ("unreachable_entry", smt.VerificationResult.OK),
    ("straight_into_loop", smt.VerificationResult.OK),
    ("overflow2", smt.VerificationResult.FAIL),
    ("greater_than_op", smt.VerificationResult.OK),
))
def test_dsa_examples(func_name: str, expected: smt.VerificationResult) -> None:
    _, functions, _ = example_dsa_CFunctions
    if "fail_" in func_name:
        pytest.skip(
            "TODO: add proof obligations to make sure variables are defined before being used")

    actual = verify(functions['tmp.' + func_name])
    assert expected == actual


assert len(test_dsa_examples.pytestmark[0].args[1]) == len(   # type: ignore
    example_dsa_CFunctions[1]), "not all/too many functions are tested"


@pytest.mark.parametrize('func_name', test_CFunctions[1].keys())
def test_main(func_name: str) -> None:
    should_fail = '_fail_' in func_name or func_name.endswith(
        '_fail') or func_name.startswith('fail_')
    _, functions, _ = test_CFunctions
    result = verify(functions[func_name])
    if result is smt.VerificationResult.FAIL:
        assert should_fail
    elif result is smt.VerificationResult.OK:
        assert not should_fail
    else:
        assert False, f"unexpected verification result {result}"
