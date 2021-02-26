from time import monotonic

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


@pytest.mark.parametrize('expr', [
    # actual errors
    '[1,2,3,4].hello',
    'hello',
    'hello.world',
    '[1,2,3](2)',
    '4[0]',
    '4[:4]',
    '4.1[0]',
    'True[0]',
    '4.1[:4]',
    '1.2 + "a"',
    '4 / "a"',
    '"b" / "a"',
    '"b" // "a"',
    '"b" % "a"',
    '1 @ 2',
    'len(12)',
    '12 ** "hello"',
    'int([])',
    'float([])',
    '~"a"',
    '~3.14',
    '3.1 | 4.2',

    # temporary unsupported
    '()',
    '{}',
    'dict()',
    '[1,2,3,4][::2]',
    'str(12.34)',
    '(4).bit_length()',
    'min([], default=13)',
])
def test_type_error(expr):
    proof = prove_f(f"""
        def f():
            assert {expr}
    """)
    assert proof.conclusion == Conclusion.SKIP
    assert type(proof.error) is UnsupportedError


def test_partial_proof():
    proof = prove_f("""
        def f():
            assert True
            hello
            assert False  # is not reached
    """)
    assert proof.conclusion == Conclusion.PARTIAL
    assert type(proof.error) is UnsupportedError
