# external
import pytest

# project
from deal_solver import Conclusion

# app
from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # compare
    '[1, 2, 3] == [1, 2, 3]',
    '[1, 2, 3] != [1, 2, 3, 3]',
    '[] == []',
    '[] + [] == [] + [] + []',
    '[] != [1]',
    '[1] != []',

    # compare mismatching types
    '[1] != {1}',
    '[1] != {1: 2}',
    '[1] != ""',
    '[1] != 1',
    '[1] != 1.2',
    '[] != {1}',
    '[] != {1: 2}',
    '[] != ""',
    '[] != 1',
    '[] != 1.2',

    # contains
    '10 in [3, 6, 10, 17]',
    '11 not in [3, 6, 10, 17]',
    'not "" in [3]',
    'not "" in []',
    '""  not in []',
    '12  not in []',

    # index
    '[4, 5, 6][1] == 5',
    '[4, 5, 6, 7, 8][2:4] == [6, 7]',
    '[4, 5, 6, 7, 8][2:] == [6, 7, 8]',
    '[4, 5, 6, 7, 8][:4] == [4, 5, 6, 7]',
    '[1, 2, 3][:] == [1, 2, 3]',
    '[][:] == []',
    '[][:3] == []',

    # operations
    '[1] + [2] == [1, 2]',
    '[1, 2] + [3, 4] == [1, 2, 3, 4]',
    '[] + [] == []',
    # '[1] * 3 == [1, 1, 1]',
    '([] + [True] + [False])[0] == True',

    # methods
    '[7, 8, 8, 9].index(8) == 1',
    '[7, 8, 8, 9].index(8, 2) == 2',
    '[1, 2, 4, 6, 5, 6].count(6) == 2',
    '[1, 1, 1].count(1) == 3',
    '[1, 1, 1].count(2) == 0',
    '[].count(2) == 0',
    '[1, 2, 3].copy() == [1, 2, 3]',

    # functions
    'len([7, 9, 9, 9, 11]) == 5',
    'min([7, 3, 5]) == 3',
    'max([3, 7, 5]) == 7',
    'sum([3, 7, 5]) == 15',
    'sum([sum([3, 7]), 5]) == 15',
    'bool([]) == False',
    'bool([0]) == True',

    # implicit bool
    'not []',
    '[1]',
    '[1, 2]',
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
