import math

import hypothesis
import hypothesis.strategies
import pytest
from z3 import Z3Exception

from deal_solver import Conclusion
from deal_solver._proxies import FloatSort

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

    # math for bool
    'True + True == 2',
    'True - True == 0',
    'True * True == 1',
    'True / True == 1.0',
    'True // True == 1',
    'True % True == 0',
    '~True == -2',

    # implicit bool to int
    '2 + True == 3',
    '2 - True == 1',
    '2 * True == 2',
    '2 ** True == 2',
    '2 / True == 2.0',
    '+True == 1',
    '-True == -1',

    # implicit bool to float
    '2.3 + True == 3.3',
    '2.4 - True == 1.4',
    '2.3 * True == 2.3',
    # '2.3 ** True == 2.3',
    '2.3 / True == 2.3',

    # bool functions
    'int(True) == 1',
    'int(False) == 0',
    'float(True) == 1.0',
    'float(False) == 0.0',
    'bool(True)',
    'not bool(False)',

    # other expressions
    'True if True else False',
    'False if False else True',

    # empty sequences
    # 'len(set()) == 0',
    'len([]) == 0',
    'len("") == 0',
    '"" == ""',

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
    '8.0 // float("-inf") == -1.0',
    '-8.0 // float("-inf") == 0.0',
    '0.0 // float("inf") == 0.0',
    'float("NaN") != 2.3',
])
def test_assert_ok_fp_only(check: str):
    assert eval(check)
    text = """
        from typing import List
        def f():
            assert {}
    """
    text = text.format(check)

    old_prefer_real = FloatSort.prefer_real
    try:
        FloatSort.prefer_real = False
        theorem = prove_f(text)
        assert theorem.conclusion is Conclusion.OK

        FloatSort.prefer_real = True
        try:
            theorem = prove_f(text)
        except Z3Exception:
            pass
        else:
            assert theorem.conclusion in (Conclusion.SKIP, Conclusion.FAIL)
    finally:
        FloatSort.prefer_real = old_prefer_real


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


@pytest.mark.parametrize('expr', [
    '1.2 + 3.4',
    '1.2 - 3.4',
    '1.2 * 3.4',
    '1.2 // 3.4',
    '1.2 / 3.4',
    '4.3 % 2.1',
    '3.5 + 3',
    '3.5 - 3',
    '3.5 * 3',
    '3.5 / 3',
    '3.5 // 3',
    '3.5 % 3',
])
def test_float(prefer_real: bool, expr: str):
    expected = eval(expr)
    theorem = prove_f(f"""
        import math
        def f():
            assert math.isclose({expr}, {expected})
    """)
    assert theorem.conclusion is Conclusion.OK


@hypothesis.settings(report_multiple_bugs=False)
@hypothesis.given(
    left=hypothesis.strategies.integers(),
    right=hypothesis.strategies.integers(),
    op=hypothesis.strategies.sampled_from([
        '+', '-', '*', '/', '%', '//',
        '<', '<=', '==', '!=', '>=', '>',
    ]),
)
def test_fuzz_math_int(left, right, op):
    expr = '{l} {op} {r}'.format(l=left, op=op, r=right)
    expected = 0
    try:
        expected = eval(expr)
    except ZeroDivisionError:
        hypothesis.reject()

    text = """
        import math
        def f():
            assert math.isclose({expr}, {expected})
    """
    text = text.format(expr=expr, expected=expected)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


float_strategy = hypothesis.strategies.one_of(
    hypothesis.strategies.floats(min_value=.005),
    hypothesis.strategies.floats(max_value=-.005),
)


@hypothesis.settings(report_multiple_bugs=False)
@hypothesis.given(
    left=float_strategy,
    right=float_strategy,
    op=hypothesis.strategies.sampled_from([
        '+', '-', '*', '/', '//',
        '==', '!=', '<=', '<', '>=', '>',
    ]),
)
def test_fuzz_math_floats(left, right, op):
    expr = '{l} {op} {r}'.format(l=left, op=op, r=right)
    expected = eval(expr, {'inf': math.inf})
    if math.isinf(expected):
        hypothesis.reject()

    text = """
        import math
        def f():
            inf = float('inf')
            nan = float('nan')
            assert math.isclose({expr}, {expected})
    """
    text = text.format(expr=expr, expected=expected)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
