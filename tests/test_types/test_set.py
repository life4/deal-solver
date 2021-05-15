import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # compare
    '{1, 2, 3} == {1, 2, 3}',
    '{1, 2, 3} != {1, 2, 3, 4}',
    '{1, 2, 3} == {3, 1, 2}',
    '{1, 2, 3} == {3, 2, 1, 1, 2}',
    'set() != {1}',
    '{1} != set()',
    'set() == set()',

    # compare mismatching types
    '{1} != [1]',
    '{1} != {1: 2}',
    '{1} != "hi"',
    '{1} != 1',
    '{1} != True',

    # 'len({7, 9, 9, 9, 11}) == 3',

    # operations
    '10 in {3, 6, 10, 17}',
    '2 not in {3, 6, 10, 17}',
    '{1, 2} | {2, 3} == {1, 2, 3}',
    '{1, 2} ^ {2, 3} == {1, 3}',
    '{1, 2} & {2, 3} == {2}',

    # methods
    '{1, 2}.union({2, 3}) == {1, 2, 3}',
    '{1, 2}.intersection({2, 3}) == {2}',
    '{1, 2}.symmetric_difference({2, 3}) == {1, 3}',
    '{1, 2}.difference({2, 3}) == {1}',
    '{1, 2}.copy() == {1, 2}',

    # is* methods
    '{1, 2}.issubset({1, 2, 3})',
    'not {1, 2, 3}.issubset({1, 2})',
    '{1, 2, 3}.issuperset({1, 2})',
    'not {1, 2}.issuperset({1, 2, 3})',
    '{1, 2}.isdisjoint({3, 4})',
    'not {1, 2}.isdisjoint({2, 3})',

    # functions
    'len({True}) >= 1',
    'len({4}) >= 1',
    'len({4, 5, 5, 6}) >= 3',
    'len(set()) == 0',
    'set({1, 2}) == {1, 2}',
])
def test_expr_asserts_ok(check: str) -> None:
    assert eval(check)
    text = """
        from typing import List
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


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


def test_set_add():
    theorem = prove_f("""
        def f():
            a = set()
            a.add(1)
            assert a == {1}
            a.add(2)
            assert a == {1, 2}
            a.add(2)
            assert a == {1, 2}
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


def test_set_pop():
    theorem = prove_f("""
        def f():
            a = {1}
            v = a.pop()
            assert v == 1
            assert a == set()
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_pop_two():
    theorem = prove_f("""
        def f():
            a = {1, 2}
            v = a.pop()
            assert (v == 1 and a == {2}) or (v == 2 and a == {1})
    """)
    assert theorem.conclusion is Conclusion.OK


def test_set_pop_empty():
    theorem = prove_f("""
        def f():
            a = set()
            a.pop()
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError: pop from an empty set'
