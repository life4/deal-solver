# external
import pytest

# project
from deal_solver import Conclusion

# app
from .helpers import prove_f


@pytest.mark.parametrize('expr, err', [
    ('3.1 | 4.2', "unsupported operand type(s) for bitwise operation: 'float' and 'float'"),

    # get attr
    ('4[0]',      "'int' object is not subscriptable"),
    ('4.1[0]',    "'float' object is not subscriptable"),
    ('True[0]',   "'bool' object is not subscriptable"),

    # get slice
    ('4[:4]',     "'int' object is not subscriptable"),
    ('4.1[:4]',   "'float' object is not subscriptable"),
    ('True[:4]',  "'bool' object is not subscriptable"),

    # binary operations for int
    ('3 - ""',    "unsupported operand type(s) for -: 'int' and 'str'"),
    ('3 @ 3',     "unsupported operand type(s) for @: 'int' and 'int'"),
    ('3 * set()', "unsupported operand type(s) for *: 'int' and 'set'"),
    ('3 ** ""',   "unsupported operand type(s) for **: 'int' and 'str'"),
    ('3 + ""',    "unsupported operand type(s) for +: 'int' and 'str'"),
    ('4 / "a"',   "unsupported operand type(s) for /: 'int' and 'str'"),
    ('4 // "a"',  "unsupported operand type(s) for //: 'int' and 'str'"),
    ('4 % "a"',   "unsupported operand type(s) for %: 'int' and 'str'"),

    # binary operations for float
    ('4.1 - []',  "unsupported operand type(s) for -: 'float' and 'list'"),
    ('4.1 @ []',  "unsupported operand type(s) for @: 'float' and 'list'"),
    ('4.1 * []',  "unsupported operand type(s) for *: 'float' and 'list'"),
    ('4.1 ** []', "unsupported operand type(s) for **: 'float' and 'list'"),
    ('4.1 / []',  "unsupported operand type(s) for /: 'float' and 'list'"),
    ('4.1 // []', "unsupported operand type(s) for //: 'float' and 'list'"),
    ('4.1 % []',  "unsupported operand type(s) for %: 'float' and 'list'"),
    ('4.1 + []',  "unsupported operand type(s) for +: 'float' and 'list'"),

    # unary operations for float
    ('~3.14',     "bad operand type for unary ~: 'float'"),

    # binary operations for str
    ('"" * ""',   "unsupported operand type(s) for *: 'str' and 'str'"),
    ('"a" - 3',   "unsupported operand type(s) for -: 'str' and 'int'"),
    ('"a" @ 3',   "unsupported operand type(s) for @: 'str' and 'int'"),
    ('"a" ** 3',  "unsupported operand type(s) for **: 'str' and 'int'"),
    ('"a" / 3',   "unsupported operand type(s) for /: 'str' and 'int'"),
    ('"a" // 3',  "unsupported operand type(s) for //: 'str' and 'int'"),
    ('"a" % 3',   "unsupported operand type(s) for %: 'str' and 'int'"),
    ('"a" + 3',   "unsupported operand type(s) for +: 'str' and 'int'"),

    # unary operations for str
    ('+"a"',     "bad operand type for unary +: 'str'"),
    ('-"a"',     "bad operand type for unary -: 'str'"),
    ('~"a"',     "bad operand type for unary ~: 'str'"),

    # binary operations for list
    ('[] - 3',   "unsupported operand type(s) for -: 'list' and 'int'"),
    ('[] @ 3',   "unsupported operand type(s) for @: 'list' and 'int'"),
    ('[] ** 3',  "unsupported operand type(s) for **: 'list' and 'int'"),
    ('[] / 3',   "unsupported operand type(s) for /: 'list' and 'int'"),
    ('[] // 3',  "unsupported operand type(s) for //: 'list' and 'int'"),
    ('[] % 3',   "unsupported operand type(s) for %: 'list' and 'int'"),
    ('[] + ""',  'can only concatenate list (not "str") to list'),

    # unary operations for list
    ('+[]',      "bad operand type for unary +: 'list'"),
    ('-[]',      "bad operand type for unary -: 'list'"),
    ('~[]',      "bad operand type for unary ~: 'list'"),

    # binary operations for set
    ('{1} - 3',  "unsupported operand type(s) for -: 'set' and 'int'"),
    ('{1} @ 3',  "unsupported operand type(s) for @: 'set' and 'int'"),
    ('{1} * 3',  "unsupported operand type(s) for *: 'set' and 'int'"),
    ('{1} ** 3', "unsupported operand type(s) for **: 'set' and 'int'"),
    ('{1} / 3',  "unsupported operand type(s) for /: 'set' and 'int'"),
    ('{1} // 3', "unsupported operand type(s) for //: 'set' and 'int'"),
    ('{1} % 3',  "unsupported operand type(s) for %: 'set' and 'int'"),
    ('{1} + 3',  "unsupported operand type(s) for +: 'set' and 'int'"),

    # unary operations for set
    ('-{1}',     "bad operand type for unary -: 'set'"),
    ('+{1}',     "bad operand type for unary +: 'set'"),
    ('~{1}',     "bad operand type for unary ~: 'set'"),

    # binary operations for bool
    ('True - []',       "unsupported operand type(s) for -: 'bool' and 'list'"),
    ('True @ []',       "unsupported operand type(s) for @: 'bool' and 'list'"),
    ('True * set()',    "unsupported operand type(s) for *: 'bool' and 'set'"),
    ('True ** []',      "unsupported operand type(s) for **: 'bool' and 'list'"),
    ('True / []',       "unsupported operand type(s) for /: 'bool' and 'list'"),
    ('True // []',      "unsupported operand type(s) for //: 'bool' and 'list'"),
    ('True % []',       "unsupported operand type(s) for %: 'bool' and 'list'"),
    ('True + []',       "unsupported operand type(s) for +: 'bool' and 'list'"),

])
def test_type_error__table(prefer_real, expr, err):
    with pytest.raises(TypeError):
        eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'


@pytest.mark.parametrize('left', ['""', '[]', 'set()', '1', '3.4', 'True'])
@pytest.mark.parametrize('right', ['""', '[]', 'set()', '1', '3.4', 'True'])
@pytest.mark.parametrize('op', ['+', '-', '*', '**', '/', '//', '%', '@'])
def test_type_error_bin_op(prefer_real: bool, left: str, op: str, right: str):
    expr = f'{left} {op} {right}'

    try:
        eval(expr)
    except TypeError:
        pass
    else:
        return
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description.startswith('TypeError')
