from deal_solver import Conclusion
from ..helpers import prove_f


def test_dict_clear():
    theorem = prove_f("""
        def f():
            a = {1: 2, 3: 4}
            a.clear()
            a[1]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'


def test_dict_getattr_fails():
    theorem = prove_f("""
        def f():
            a = {1: 2}
            a[2]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'
