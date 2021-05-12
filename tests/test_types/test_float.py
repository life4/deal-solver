import pytest
from deal_solver import Conclusion
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
