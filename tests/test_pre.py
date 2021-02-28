# project
from deal_solver import Conclusion

# app
from .helpers import prove_f


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
