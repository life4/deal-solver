import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # compare
    '(1, 2) == (1, 2)',
    '(1, 2) != (2, 1)',
    '(1, 2) != (2, 1)',
    '() != (2, 1)',
    '(1, 2) != ()',
    '() != (2.1,)',
    '(1.2,) != ()',
    '() == ()',

    # compare mismatching types
    '(1,) != {1}',
    '(1,) != {1: 2}',
    '(1,) != ""',
    '(1,) != 1',
    '(1,) != 1.4',
    # '(1,) != [1]',
    '() != {1}',
    '() != {1: 2}',
    '() != ""',
    '() != 1',
    '() != 1.4',
    # '() != [1]',

    # operators
    '(1, 2) + (3,) == (1, 2, 3)',
    '(1, 2) + () == (1, 2)',
    '() + () == ()',
    '1 not in ()',
    '2 in (1, 2, 3)',
    '4 not in (1, 2, 3)',

    # getitem
    '()[:3] == ()',

    # functions
    'len(()) == 0',
    'len((1, 5, 7)) == 3',

    # implicit bool
    'not ()',
    '(1, 2)',

    # methods
    '(1, 2, 1, 1).count(1) == 3',
    '(1, 2, 1, 1).count(4) == 0',
    '().count(4) == 0',
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


@pytest.mark.parametrize('check, error', [
    ('()[0]',           'IndexError: tuple index out of range'),
    ('(1, 2)[6]',       'IndexError: tuple index out of range'),
    ('().index(2)',     'ValueError: tuple.index(x): x not in tuple'),
    ('(1,).index(2)',   'ValueError: tuple.index(x): x not in tuple'),
])
def test_expr_exception(check: str, error: str) -> None:
    with pytest.raises(Exception):
        eval(check)
    text = """
        from typing import List
        def f():
            {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.FAIL
    assert theorem.description == error
