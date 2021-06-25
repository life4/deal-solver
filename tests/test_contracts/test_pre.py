from deal_solver import Conclusion

from ..helpers import prove_f


def test_pre_condition_ok():
    theorem = prove_f("""
        @deal.pre(lambda a: a > 10)
        def f(a: int) -> int:
            assert a > 5
    """)
    assert theorem.conclusion is Conclusion.OK


def test_pre_condition_fail():
    theorem = prove_f("""
        @deal.pre(lambda a: a > 5)
        def f(a: int) -> int:
            assert a > 10
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_pre_assert_conflict_prefer_assert():
    """
    If pre-condition doesn't match with assertions,
    show counter-exampel for assertion, not pre-condition.
    """
    proof = prove_f("""
        @deal.pre(lambda a: a > 5)
        def f(a: int) -> int:
            assert a > 10
    """)
    assert proof.conclusion is Conclusion.FAIL
    assert str(proof.example) == 'a=6'

    proof = prove_f("""
        @deal.pre(lambda a: a == 6)
        def f(a: int) -> int:
            assert a == 7
    """)
    assert proof.conclusion is Conclusion.FAIL
    assert str(proof.example) == 'a=6'


def test_pre_cannot_resolve():
    theorem = prove_f("""
        @deal.pre(unknown)
        @deal.pre(lambda a: a > 5)
        def f(a: int) -> int:
            assert a > 3
    """)
    assert theorem.conclusion is Conclusion.OK


def test_pre_ignore_empty():
    theorem = prove_f("""
        @deal.pre(lambda: True)
        def f() -> int:
            assert True
    """)
    assert theorem.conclusion is Conclusion.OK
