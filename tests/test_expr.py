import pytest

from deal_solver import Conclusion

from .helpers import prove_f


@pytest.mark.parametrize('check', [
    # logic
    'True',
    'not False',
    'True and True',
    'True or True',
    'False or True',
    'True or False',

    # math for int and float
    '1 + 2.0 == 3.0',
    '1.0 + 2 == 3.0',
    '1 - 2.0 == -1.0',
    '1.0 - 2 == -1.0',
    '1 * 2.0 == 2.0',
    '1.0 * 2 == 2.0',
    '1 / 2.0 == 0.5',
    '1.0 / 2 == 0.5',
    '1.0 % 2 == 1.0',

    # complex math
    '3 + 5 + 7 == 15',
    '3 * 5 * 2 == 30',
    '3 + 5 * 2 == 13',

    # other expressions
    'True if True else False',
    'False if False else True',

    # sequences in sequences
    'len([""]) == 1',
    'len([[]]) == 1',
    'len([[], []]) == 2',

    # converters
    'not bool(0)',
    'bool(1)',
    'bool(2)',
    'bool(-2)',
    'not bool("")',
    'bool("abc")',
    'not bool([])',
    'bool([1, 2])',
    'bool([[]])',
    'not bool(())',
    'bool((1,))',
    'bool(((),))',
    'int(1) == 1',
    'int(1.5) == 1',
    'int("12") == 12',

    # implicit bool
    'not 0',
    '1',
    '1 and 3',
    '0 or 3',
    '2 if 3 else 0',
    '0 if 0 else 4',
    'int',

    # comprehensions
    '[i for i in [4, 5, 6]] == [4, 5, 6]',
    '[i + i for i in [4, 5, 6]] == [8, 10, 12]',
    '[i for i in [4, 5, 6] if i != 5] == [4, 6]',
    '[i+i for i in [4, 5, 6, 7, 8] if i % 2 == 0] == [8, 12, 16]',

    # compare int and float
    '2 > 1.5',
    '2 >= 1.5',
    '1 < 1.5',
    '1 <= 1.5',
    '1 != 1.5',
    '0 == 0.0',

    # compare float and int
    '1.5 > 1',
    '1.5 >= 1',
    '1.5 < 2',
    '1.5 <= 2',
    '1.5 != 2',
    '0.0 == 0',

    # compare mismatching empty types
    'set() != []',
    'not (set() == [])',
])
def test_asserts_ok(prefer_real: bool, check: str) -> None:
    assert eval(check)
    text = """
        from typing import List
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    'False',
    'not True',
    'True and False',
    'False and True',
    'False and False',
    'False or False',
    '13 == -13',
    '3 + 6 == 10',
    'False if True else True',
    'True if False else False',
])
def test_asserts_fail(check: str) -> None:
    assert not eval(check)
    text = """
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.FAIL


def test_lambda_one_arg():
    theorem = prove_f("""
        def f():
            a = lambda x: x * 2
            assert a(3) == 6
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_two_args():
    theorem = prove_f("""
        def f():
            a = lambda x, y: x - y
            assert a(7, 3) == 4
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_no_args():
    theorem = prove_f("""
        def f():
            a = lambda: 13
            assert a() == 13
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_untyped():
    theorem = prove_f("""
        def f():
            a = lambda x: x + x
            assert a(3) == 6
            assert a("ab") == "abab"
    """)
    assert theorem.conclusion is Conclusion.OK


VALUES = [
    # regular concrete types
    '""', '1', 'True',  '3.4',
    # empty generics
    '[]',  '()',  'set()',  '{}',
    # non-empty generic containers
    '[1]', '(1, )', '{1}', '{1: 2}',
]


@pytest.mark.parametrize('left', VALUES)
@pytest.mark.parametrize('right', VALUES)
def test_equality(prefer_real: bool, left: str, right: str):
    expr = f'{left} == {right}'
    if not eval(expr):
        expr = f'{left} != {right}'
    assert eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.OK
