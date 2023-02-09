import pytest
import abc_cfg
import source
import nip
import dsa
import assume_prove
import smt
import syntax
import ghost_data

# global variables are bad :(
syntax.set_arch('rv64')


with open('examples/kernel_CFunctions.txt') as f:
    kernel_CFunctions = syntax.parse_and_install_all(f, None)

with open('tests/all.txt') as f:
    test_CFunctions = syntax.parse_and_install_all(f, None)

with open('examples/dsa.txt') as f:
    example_dsa_CFunctions = syntax.parse_and_install_all(f, None)
del f


def verify(filename: str, unsafe_func: syntax.Function) -> smt.VerificationResult:
    prog_func = source.convert_function(unsafe_func).with_ghost(
        ghost_data.get(filename, unsafe_func.name))
    nip_func = nip.nip(prog_func)
    dsa_func = dsa.dsa(nip_func)
    prog = assume_prove.make_prog(dsa_func)
    smtlib = smt.make_smtlib(prog)
    sats = tuple(smt.send_smtlib_to_z3(smtlib))
    return smt.parse_sats(sats)


def do_test(filename: str, func: syntax.Function) -> None:
    suffix = func.name.split('.')[-1]
    should_fail = False
    should_fail = should_fail or '_fail_' in suffix
    should_fail = should_fail or suffix.endswith('_fail')
    should_fail = should_fail or suffix.startswith('fail_')
    should_fail = should_fail or '_fails_' in suffix
    should_fail = should_fail or suffix.endswith('_fails')
    should_fail = should_fail or suffix.startswith('fails_')

    result = verify(filename, func)
    if should_fail:
        assert result is smt.VerificationResult.FAIL
    else:
        assert result is smt.VerificationResult.OK


@pytest.mark.parametrize('func_name', example_dsa_CFunctions[1].keys())
def test_dsa(func_name: str) -> None:
    do_test('examples/dsa.c', example_dsa_CFunctions[1][func_name])


@pytest.mark.parametrize('func_name', test_CFunctions[1].keys())
def test_main(func_name: str) -> None:
    do_test('tests/all.c', test_CFunctions[1][func_name])
