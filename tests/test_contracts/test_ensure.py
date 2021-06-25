from deal_solver import Conclusion

from ..helpers import prove_f


def test_ok():
    theorem = prove_f("""
        @deal.ensure(lambda a, result: result >= a)
        def f(a: int) -> int:
            return a * a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_fail():
    theorem = prove_f("""
        @deal.ensure(lambda result: result != a)
        def f(a: int) -> int:
            return 12
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert theorem.example is not None
    assert dict(theorem.example)['a'] == 12


def test_cannot_resolve():
    theorem = prove_f("""
        @deal.ensure(unknown)
        @deal.ensure(lambda a, result: result >= 0)
        def f(a: int) -> int:
            return a * a
    """)
    assert theorem.conclusion is Conclusion.OK
