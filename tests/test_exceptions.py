from deal_solver import Conclusion

# app
from .helpers import prove_f


def test_ok():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ValueError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_fail():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ZeroDivisionError
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_subclasses_builtin():
    theorem = prove_f("""
        @deal.raises(LookupError)
        def f():
            raise IndexError
    """)
    assert theorem.conclusion is Conclusion.OK
