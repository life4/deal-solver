import pytest
from deal_solver import Conclusion
from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # contains
    '1 not in {}',
    '1 in {1: 2}',
    '3 in {1: 2, 3: 4}',
    '2 not in {1: 2}',

    # getitem
    '{1: 2}[1] == 2',

    # compare
    '{} == {}',
    '{1: 2} == {1: 2}',
    '{1: 2} != {2: 1}',
    '{1: 2} != {}',
    '{} != {1: 2}',

    # methods
    '{1: 2}.get(1, 3) == 2',
    '{1: 2}.get(3, 4) == 4',
    '{}.get(1, 2) == 2',
])
def test_asserts_ok(check: str) -> None:
    assert eval(check)
    text = """
        from typing import List
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


def test_dict_clear():
    theorem = prove_f("""
        def f():
            a = {1: 2, 3: 4}
            a.clear()
            a[1]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'


def test_dict_clear_empty():
    theorem = prove_f("""
        def f():
            a = {}
            a.clear()
            assert a == {}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_dict_getattr_fails():
    theorem = prove_f("""
        def f():
            a = {1: 2}
            a[2]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'


def test_dict_getattr_fails_empty():
    theorem = prove_f("""
        def f():
            a = {}
            a[0]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'
