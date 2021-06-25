import math
import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    'math.isclose(5, 5)',
    'math.isclose(5.0, 5)',
    'math.isclose(5, 5.0)',
    'not math.isclose(5, 4)',
    'math.isclose(7.8 / 2.5, 3.12)',
    'math.isclose(2.7 - 1.4, 1.3)',

    'math.isclose(math.e, 2.718281828459045)',
    'math.isclose(math.pi, 3.141592653589793)',
    'math.isclose(math.pi/2, 1.5707963267948966)',
    'math.isclose(math.tau, 6.283185307179586)',
    'math.isclose(1.5, 2.5, 1e-07, 1.1)',

    'math.isinf(math.inf)',
    'math.isinf(float("inf"))',
    'math.isinf(float("-inf"))',
    'not math.isinf(123)',
    'not math.isinf(123 / 5)',
    'not math.isinf(123.456)',
    'not math.isinf(float("nan"))',

    'math.isnan(math.nan)',
    'math.isnan(float("nan"))',
    'not math.isnan(123)',
    'not math.isnan(123 / 5)',
    'not math.isnan(123.456)',
    'not math.isnan(float("inf"))',
    'not math.isnan(float("-inf"))',

    'math.isclose(math.sin(0), 0.0)',
    'math.isclose(math.sin(math.pi/2), 1, 1e-07)',
    'math.isclose(math.sin(-math.pi/2), -1, 1e-07)',

    'math.trunc(12) == 12',
    'math.trunc(-12) == -12',
    'math.trunc(12.9) == 12',
    'math.trunc(-12.9) == -12',
    'math.trunc(-12.0) == -12',

    # constants
    'math.pi == 3.141592653589793',
    'math.e == 2.718281828459045',
    'math.tau == math.pi * 2',
    'math.inf > 1000',
    'math.inf != math.nan',
])
def test_math_module(prefer_real: bool, check: str) -> None:
    # assert eval(check, dict(math=math))
    text = """
        import math

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('expr, exc, msg', [
    ('math.isclose("", "")', TypeError, 'must be real number, not str'),
    ('math.isclose(1, "")', TypeError, 'must be real number, not str'),
    ('math.isclose("", 1)', TypeError, 'must be real number, not str'),
])
def test_exc(expr: str, exc, msg: str) -> None:
    with pytest.raises(exc):
        eval(expr, dict(math=math))
    text = """
        import math

        def f():
            {}
    """
    text = text.format(expr)
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.FAIL
    assert proof.description == f'{exc.__name__}: {msg}'


def test_unsupported():
    text = """
        import math

        def f():
            math.atan2(0, 0)
    """
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.SKIP
    assert str(proof.error) == 'no definition for math.atan2'
