import pytest
import hypothesis
import hypothesis.strategies

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # comparison
    '1 != 2',
    '2 == 2',
    '3 < 4',
    '3 <= 4',
    '4 <= 4',
    '4 >= 4',
    '5 >= 4',
    '5 > 4',
    '(5 > 4) and (7 > 3)',

    # math
    '13 == 13',
    '+12 == 12',
    '12 == --12',
    '-13 == -13',
    '+13 == --13',
    '3 + 6 == 9',
    '7 - 4 == 3',
    '7 * 4 == 28',
    '10 / 5 == 2.0',
    # '12 / 5 == 2.4',
    '13 // 5 == 2',
    '-13 // 5 == -3',
    '13 // -5 == -3',
    '13 % 5 == 3',
    '-5 % 2 == 1',
    '-1 % 3 == 2',
    '1 % -3 == -2',
    '5 % -2 == -1',
    '2 ** 3 == 8',

    # bitwise math
    '2 | 4 == 6',
    '3 & 6 == 2',
    '3 ^ 6 == 5',
    '6 << 1 == 12',
    '6 >> 1 == 3',
    '~3 == -4',
    '~-6 == 5',
    '~0 == -1',

    # functions
    'bool(0) == False',
    'bool(1) == True',
    'bool(14) == True',
    'bool(-23) == True',
    'abs(12) == 12',
    'abs(-13) == 13',
    'min(13, 5) == 5',
    'min(5, 13) == 5',
    'max(13, 5) == 13',
    'max(5, 13) == 13',
    'float(4) == 4.0',
    'str(42) == "42"',

    # methods
    '(12).conjugate() == 12',
    '(12).real == 12',
    '(12).numerator == 12',
    '(12).denominator == 1',
    '(12).imag == 0',
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


@pytest.mark.parametrize('left', ['1', '0', '-1'])
@pytest.mark.parametrize('right', ['1', '0', '-1', 'True', '1.0', '(5/2)'])
@pytest.mark.parametrize('op', [
    '+', '-', '*', '%', '/', '//',
    '==', '<=', '<', '>=', '>', '!=',
])
def test_operations(left: str, right: str, op: str):
    expr = f'{left} {op} {right}'
    try:
        result = eval(expr)
    except ZeroDivisionError:
        return
    expr = f'({expr}) == {result}'
    assert eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.OK
