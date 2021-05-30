import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # compare
    'True == True',
    'False == False',
    'True != False',
    'False != True',

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
    'bool(True) == True',
    'bool(False) == False',
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
