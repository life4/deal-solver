from deal_solver import Conclusion
from ..helpers import prove_f


def test_set_clear():
    theorem = prove_f("""
        def f():
            a = {1, 2, 3}
            a.clear()
            assert a == set()
            a.add(1)
            assert a == {1}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_update():
    theorem = prove_f("""
        def f():
            a = {1, 2}
            a.update({2, 3})
            assert a == {1, 2, 3}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_discard():
    theorem = prove_f("""
        def f():
            a = {1, 2, 3}
            a.discard(2)
            assert a == {1, 3}
            a.discard(2)
            assert a == {1, 3}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_remove():
    theorem = prove_f("""
        def f():
            a = {1, 2, 3}
            a.remove(2)
            assert a == {1, 3}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_remove_fails():
    theorem = prove_f("""
        def f():
            a = {1, 2, 3}
            a.remove(2)
            a.remove(2)
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'
