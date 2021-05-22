import math
import pytest
import hypothesis
import hypothesis.strategies
from z3 import Z3Exception

from deal_solver import Conclusion
from deal_solver._proxies import FloatSort

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # math
    '1.4 + 2.7 == 4.1',
    '2.9 - 1.4 == 1.5',
    '7.0 % 3.0 == 1.0',
    '7.0 % 3.5 == 0.0',
    # 'math.isclose(4.5 ** 2, 20.25)',
    '5.0 / 2.0 == 2.5',
    '(1/2) / (4/3) == 0.375',
    '7.3 // 2.0 == 3.0',
    '7.3 // -2.0 == -4.0',
    '-7.3 // 2.0 == -4.0',
    '0.005 // 0.005 == 1.0',

    # compare
    '2.7 > 1.4',
    '1.4 < 2.7',
    '2.7 == 2.7',
    'float("nan") != float("nan")',
    'float("inf") == float("inf")',
    '-0.0 == +0.0',
    'float("NaN") != 2.3',

    # functions
    'bool(2.1) == True',
    'bool(0.0) == False',
    'int(4.2) == 4',
    'float(4.2) == 4.2',
    'float(10 / 2) == 5.0',
    'float("Inf") > 10000',
    'abs(-4.2) == 4.2',
    # 'str(4.2) == "4.2"',

    # methods
    '(12.1).conjugate() == 12.1',
    '(12.1).real == 12.1',
    '(12.1).imag == 0',
    '(12.1).is_integer() == False',
    '(12.0).is_integer() == True',
])
def test_expr_asserts_ok(prefer_real: bool, check: str) -> None:
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


VALUES = ['1.0', '1.1', 'float("nan")', '0.0', '-1.0', '-1.1', '(5/2)']


@pytest.mark.parametrize('left', VALUES)
@pytest.mark.parametrize('right', VALUES + ['True', '1'])
@pytest.mark.parametrize('op', [
    '+', '-', '*', '%', '/', '//',
    '==', '<=', '<', '>=', '>', '!=',
])
def test_operations(prefer_real: bool, left: str, right: str, op: str):
    expr = f'{left} {op} {right}'
    try:
        result = eval(expr)
    except ZeroDivisionError:
        return
    if repr(result) == 'nan':
        expr = f'math.isnan({expr})'
    else:
        expr = f'({expr}) == {result}'
    assert eval(expr, dict(math=math))
    proof = prove_f(f"""
        import math
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.OK
