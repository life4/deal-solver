from time import monotonic

import pytest
import z3

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
    'set()',
    '[1,2,3,4][::2]',
    '[1,2,3,4].hello',
    'hello',
    '[1,2,3](2)',
    '4[0]',
    'str(12.34)',
])
def test_type_error(expr):
    with pytest.raises(UnsupportedError):
        prove_f(f"""
            def f():
                assert {expr}
        """)


@pytest.mark.parametrize('expr', [
    '12 ** "hello"',
])
def test_sort_mismatch(expr):
    with pytest.raises(z3.Z3Exception, match='sort mismatch'):
        prove_f(f"""
            def f():
                assert {expr}
        """)
