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
    ('[1,2,3,4].hello', 'no definition for builtins.list.hello'),
    ('hello',           'cannot resolve name hello'),
    ('hello.world',     'cannot resolve attribute hello.world'),
    ('[1,2,3](2)',      'list object is not callable'),
    ('4[0]',            'int object is not subscriptable'),
    ('4[:4]',           'int object is not subscriptable'),
    ('4.1[0]',          'float object is not subscriptable'),
    ('True[0]',         'bool object is not subscriptable'),
    ('4.1[:4]',         'float object is not subscriptable'),
    ('1.2 + "a"',       'cannot combine float and str'),
    ('4 / "a"',         'unsupported denominator type str'),
    ('"b" / "a"',       'cannot perform operation: str/str'),
    ('"b" // "a"',      'cannot perform operation: str//str'),
    ('"b" % "a"',       'cannot perform operation: str%str'),
    ('1 @ 2',           'cannot perform operation: int@int'),
    ('len(12)',         'int.__len__ is not defined'),
    ('12 ** "hello"',   'cannot perform operation: int**str'),
    ('int([])',         'cannot convert list to int'),
    ('float([])',       'cannot convert list to float'),
    ('~"a"',            'str.__invert__ is not defined'),
    ('~3.14',           'float.__invert__ is not defined'),
    ('3.1 | 4.2',       'float does not support bitwise operations'),
    ('13 in 123',       'int.__contains__ is not defined'),

    # temporary unsupported
    ('()',                  'unsupported ast node Tuple'),
    ('{}',                  'unsupported ast node Dict'),
    ('dict()',              'cannot resolve name dict'),
    ('[1,2,3,4][::2]',      'slice step is not supported'),
    ('str(12.34)',          'cannot convert float to str'),
    ('(4).bit_length()',    'no definition for builtins.int.bit_length'),
    ('min([], default=13)', 'keyword function arguments are unsupported'),
])
def test_type_error(expr, err):
    proof = prove_f(f"""
        def f():
            assert {expr}
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
