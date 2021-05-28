import pytest

from deal_solver import Conclusion, UnsupportedError

from .helpers import prove_f


@pytest.mark.parametrize('setup, ann, check', [
    # simple annotations
    ('', 'int',     'a - a == 0'),
    ('', '"int"',   'a - a == 0'),
    ('', 'float',   'a + 0.0 == a or not (a > 10 or a <= 10)'),
    ('', 'str',     'len(a) >= 0 and a.startswith(a)'),
    ('', 'str',     'len(a) >= 0'),

    # generics
    ('', 'list[int]',       '(a != []) or (a == [])'),
    ('', 'set[int]',        '(a != set()) or (a == set())'),
    ('', 'tuple[int, ...]', '(a != ()) or (a == ())'),
    ('', 'dict[str, int]',  '(a != {}) or (a == {})'),

    # typing module
    (
        'from typing import List',
        'List[int]',
        'len(a) >= 0',
    ),
    (
        'from typing import List',
        'List[int]',
        '(a != []) or (a == [])',
    ),
    (
        'from typing import Set',
        'Set[int]',
        '(a != set()) or (a == set())',
    ),
    (
        'from typing import Tuple',
        'Tuple[int, ...]',
        'len(a) >= 0',
    ),
    (
        'from typing import Dict',
        'Dict[str, int]',
        '(a != {}) or (a == {})',
    ),
    (
        'from typing import Pattern',
        'Pattern',
        'a.fullmatch',
    ),
])
def test_asserts_ok(setup: str, ann: str, check: str) -> None:
    text = """
        {s}
        def f(a: {a}):
            assert {c}
    """
    text = text.format(s=setup, a=ann, c=check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('setup, ann', [
    # too generic
    ('', 'set'),
    ('', '"set"'),
    ('', 'tuple'),

    # unsupported yet
    ('', 'tuple[int]'),
    ('', 'tuple[int, str]'),
    ('from typing import Iterator', 'Iterator[int]'),

    # unresolved names
    ('', 'unknown'),
    ('', 'unknown.type'),
    ('', 'unknown.type[0]'),
    ('', '"unknown"'),
    ('', 'int[unknown]'),
    ('', 'unknown[int]'),
    ('', 'tuple[unknown, ...]'),

    # invalid
    ('', 'int[int]'),
    ('', 'list[int:str]'),
    ('', 'list[int, str]'),
    ('', 'tuple[...]'),
    ('', 'max'),
    ('', 'max[int]'),
    ('', '"hi"[0]'),
    ('from itertools import chain', 'chain'),
    ('from itertools import chain', 'chain[int]'),
    ('from glob import glob',       'glob'),
    ('from inspect import getfile', 'getfile'),
    ('import inspect',              'inspect.getfile'),
])
def test_unsupported(setup: str, ann: str) -> None:
    proof = prove_f(f"""
        {setup}
        def f(a: {ann}):
            pass
    """)
    assert proof.conclusion == Conclusion.SKIP
    assert type(proof.error) is UnsupportedError


def test_real(prefer_real: bool) -> None:
    proof = prove_f("""
        def f(a: float):
            assert a == 0.0 or a != 0.0
    """)
    assert proof.conclusion is Conclusion.OK
