from time import monotonic

# project
from deal_solver import Conclusion, ProveError

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
    assert .5 <= monotonic() - start < .7
    assert theorem.conclusion is Conclusion.SKIP
    assert type(theorem.error) is ProveError
    assert theorem.error.args[0] == 'timeout'
