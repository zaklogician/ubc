import pytest
# FIXME: cyclic imports :(
import abc_cfg  # we have cyclic imports, and so this import is actually needed, sorry
import ghost_data
import source
import dsa
import syntax
import nip
import validate_dsa
import ghost_code

# global variables are bad :(
syntax.set_arch('rv64')

INVALID_FILENAME = "DONOTUSE/THIS/PATH/TEST_DSA_FILE.c"


with open('examples/kernel_CFunctions.txt') as f:
    kernel_CFunctions = syntax.parse_and_install_all(
        f, None)

with open('examples/dsa.txt') as f:
    example_dsa_CFunctions = syntax.parse_and_install_all(f, None)
del f


@pytest.mark.parametrize('func', (f for f in example_dsa_CFunctions[1].values() if f.entry is not None))
def test_dsa_custom_tests(func: syntax.Function) -> None:
    prog_func = source.convert_function(func).with_ghost(None)
    nip_func = nip.nip(prog_func)
    ghost_func = ghost_code.sprinkle_ghost_code(
        INVALID_FILENAME, nip_func, example_dsa_CFunctions[1])
    dsa_func = dsa.dsa(ghost_func)
    validate_dsa.validate(ghost_func, dsa_func)


@pytest.mark.slow
# sort so that the smallest functions fail first
@pytest.mark.parametrize('function', (f for f in sorted(kernel_CFunctions[1].values(), key=lambda f: len(f.nodes)) if f.entry is not None))
def test_dsa_kernel_functions(function: syntax.Function) -> None:
    print(function.name)
    if function.name in ('Kernel_C.deriveCap', 'Kernel_C.decodeCNodeInvocation'):
        pytest.skip("there's an assert true that messes DSA up")

    if function.name in ('Kernel_C.merge_regions', 'Kernel_C.create_untypeds', 'Kernel_C.reserve_region'):
        pytest.skip("loop headers change during transformation, not supported")

    if len(validate_dsa.compute_all_path(source.convert_function(function).cfg)) > 100:
        pytest.skip("too many paths, checking them all is too slow")

    if function.name in ('Kernel_C.finaliseCap', 'Kernel_C.Arch_finaliseCap'):
        pytest.skip(
            "weird if True equals False or True equals True breaks call precondition")

    prog_func = source.convert_function(function).with_ghost(None)
    nip_func = nip.nip(prog_func)
    ghost_func = ghost_code.sprinkle_ghost_code(
        INVALID_FILENAME, nip_func, kernel_CFunctions[1])
    dsa_func = dsa.dsa(ghost_func)
    validate_dsa.validate(ghost_func, dsa_func)
