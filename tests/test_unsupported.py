# stdlib
from time import monotonic

# external
import pytest

# project
from deal_solver import Conclusion, ProveError, UnsupportedError

# app
from .helpers import prove_f


def test_cannot_prove():
    theorem = prove_f("""
        def f(x: int):
            assert 2 ** x != x ** 2
    """)
    assert theorem.conclusion is Conclusion.SKIP
    assert type(theorem.error) is ProveError
    exp = 'smt tactic failed to show goal to be sat/unsat (incomplete (theory arithmetic))'
    assert theorem.error.args[0] == exp


def test_timeout():
    start = monotonic()
    theorem = prove_f("""
        from typing import List
        def f(items: List[str]):
            items.append('')
            assert items.count('') >= 1
    """, timeout=.5)
    assert .5 <= monotonic() - start < 1
    assert theorem.conclusion is Conclusion.SKIP
    assert type(theorem.error) is ProveError
    assert theorem.error.args[0] == 'timeout'


@pytest.mark.parametrize('expr, err', [
    # actual errors
    ('hello',           'cannot resolve name hello'),
    ('hello.world',     'cannot resolve attribute hello.world'),
    ('int([])',         'cannot convert list to int'),
    ('float([])',       'cannot convert list to float'),

    # temporary unsupported
    ('None',                'unsupported constant None'),
    ('2+3j',                'unsupported constant 3j'),
    ('()',                  'unsupported ast node Tuple'),
    ('{}',                  'unsupported ast node Dict'),
    ('dict()',              'cannot resolve name dict'),
    ('"ab" * 3',            'cannot multiply str'),
    ('[1] * 3',             'cannot multiply list'),
    ('[1,2,3,4][::2]',      'slice step is not supported'),
    ('str(12.34)',          'cannot convert float to str'),
    ('min([], default=13)', 'keyword function arguments are unsupported'),
    ('[1 for i in "12" for j in "34"]', 'to many loops inside list compr'),
    ('a, b = 3, 4',         'cannot assign to Tuple'),

    # unsupported attributes
    ('"Ab".swapcase()',     'unsupported attribute for type str'),
    ('(12).bit_length()',   'unsupported attribute for type int'),
])
def test_unsupported(expr, err):
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.SKIP
    assert type(proof.error) is UnsupportedError
    assert str(proof.error) == err


@pytest.mark.parametrize('expr, err', [
    ('v: UNKNOWN',          'unsupported annotation type UNKNOWN'),
    ('v: List[int]',        'unsupported annotation type List[int]'),
    ('v: list[UNKNOWN]',    'unsupported annotation type list[UNKNOWN]'),
    ('v: int[int]',         'unsupported annotation type int[int]'),
    ('v: []',               'unsupported annotation type []'),
    ('v',                   'missed annotation for v'),
])
def test_unsupported_annotations(expr, err):
    proof = prove_f(f"""
        def f({expr}):
            ...
    """)
    assert proof.conclusion == Conclusion.SKIP
    assert type(proof.error) is UnsupportedError
    assert str(proof.error) == err


def test_partial_proof():
    proof = prove_f("""
        def f():
            assert True
            hello
            assert False  # is not reached
    """)
    assert proof.conclusion == Conclusion.PARTIAL
    assert type(proof.error) is UnsupportedError
