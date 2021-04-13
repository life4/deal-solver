from deal_solver import Conclusion
from ..helpers import prove_f


def test_list_append():
    theorem = prove_f("""
        def f():
            a = []
            a.append(1)
            a.append(2)
            a.append(2)
            assert a == [1, 2, 2]
    """)
    assert theorem.conclusion is Conclusion.OK


def test_list_extend():
    theorem = prove_f("""
        def f():
            a = []
            a.extend([1, 2])
            a.extend([2])
            assert a == [1, 2, 2]
    """)
    assert theorem.conclusion is Conclusion.OK


def test_list_clear():
    theorem = prove_f("""
        def f():
            a = [1, 2, 3]
            a.clear()
            assert a == []
            a.append(1)
            assert a == [1]
    """)
    assert theorem.conclusion is Conclusion.OK


def test_list_clear_empty():
    theorem = prove_f("""
        def f():
            a = []
            assert a == []
            a.clear()
            assert a == []
    """)
    assert theorem.conclusion is Conclusion.OK
