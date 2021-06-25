from deal_solver import Conclusion

from ..helpers import prove_f


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


def test_instance_ok():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ValueError("hi")
    """)
    assert theorem.conclusion is Conclusion.OK


def test_instance_fail():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ZeroDivisionError("hi")
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_subclasses_builtin():
    theorem = prove_f("""
        @deal.raises(LookupError)
        def f():
            raise IndexError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_subclasses_custom_class():
    theorem = prove_f("""
        class Custom(IndexError):
            pass

        @deal.raises(LookupError)
        def f():
            raise Custom
    """)
    assert theorem.conclusion is Conclusion.OK
