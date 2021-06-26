import pytest

from deal_solver import Conclusion, UnsupportedError

from .helpers import prove_f


@pytest.mark.parametrize('ann, check', [
    # simple annotations
    ('int',     'a - a == 0'),
    ('"int"',   'a - a == 0'),
    ('float',   'a + 0.0 == a or not (a > 10 or a <= 10)'),
    ('str',     'len(a) >= 0 and a.startswith(a)'),
    ('str',     'len(a) >= 0'),

    # generics
    ('list[int]',       'a.append'),
    ('list["int"]',     'a.append'),
    ('set[int]',        'a.intersection'),
    ('tuple[int, ...]', '(a != ()) or (a == ())'),
    ('dict[str, int]',  'a.fromkeys'),

    # typing module
    ('typing.List[int]',        'a.append'),
    ('typing.List[int]',        '(a != []) or (a == [])'),
    ('typing.Sequence[int]',    'len(a) >= 0'),
    ('typing.Sized[int]',       'len(a) >= 0'),
    ('typing.Set[int]',         'a.add'),
    ('typing.Tuple[int, ...]',  'len(a) >= 0 and a.count'),
    ('typing.Dict[str, int]',   '(a != {}) or (a == {})'),
    ('typing.Dict[str, int]',   'a.fromkeys'),
    ('typing.Pattern',          'a.fullmatch'),
])
def test_asserts_ok(ann: str, check: str) -> None:
    theorem = prove_f(f"""
        import typing

        def f(a: {ann}):
            assert {check}
    """)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('setup, ann', [
    # too generic
    ('', 'set'),
    ('', '"set"'),
    ('', 'tuple'),
    ('import typing', 'typing.List'),

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
