from typing import Any

PLATFORM_CONTEXT_BIT_SIZE = 407


def is_global_smt(name: str) -> bool:
    return is_global_arbitrary(name)


def is_global_arbitrary(name: str) -> bool:
    return name in (
        'lc_arbitrary_1',
        'lc_arbitrary_2',
        'lc_arbitrary_3',
        'lc_arbitrary_4',
        'ghost_arbitrary_1',
        'ghost_arbitrary_2',
        'ghost_arbitrary_3',
    )
