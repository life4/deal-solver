# project
import pytest
from deal_solver import Conclusion

# app
from .helpers import prove_f


@pytest.mark.parametrize('expr, err', [
    ('~3.14',     "bad operand type for unary ~: 'float'"),
    ('~[]',       "bad operand type for unary ~: 'list'"),
    ('3.1 | 4.2', "unsupported operand type(s) for bitwise operation: 'float' and 'float'"),
    ('4[0]',      "'int' object is not subscriptable"),
    ('4[:4]',     "'int' object is not subscriptable"),
    ('4.1[0]',    "'float' object is not subscriptable"),
    ('True[0]',   "'bool' object is not subscriptable"),
    ('4.1[:4]',   "'float' object is not subscriptable"),

    ('1.2 + "a"', "unsupported operand type(s) for binary operation: 'float' and 'str'"),

    # binary operations for int
    ('4 / "a"',   "unsupported operand type(s) for /: 'int' and 'str'"),
    # ('4 // "a"',   "unsupported operand type(s) for //: 'int' and 'str'"),
    ('3 @ 3',     "unsupported operand type(s) for @: 'int' and 'int'"),

    # binary operations for str
    ('"a" - 3',   "unsupported operand type(s) for -: 'str' and 'int'"),
    ('"a" / 3',   "unsupported operand type(s) for /: 'str' and 'int'"),
    ('"a" // 3',  "unsupported operand type(s) for //: 'str' and 'int'"),
    ('"a" % 3',   "unsupported operand type(s) for %: 'str' and 'int'"),
    ('"a" ** 3',  "unsupported operand type(s) for **: 'str' and 'int'"),
    ('"a" @ 3',   "unsupported operand type(s) for @: 'str' and 'int'"),

    # unary operations for str
    ('+"a"', "bad operand type for unary +: 'str'"),
    ('-"a"', "bad operand type for unary -: 'str'"),
    ('~"a"', "bad operand type for unary ~: 'str'"),

    # binary operations for list
    ('[] - 3',   "unsupported operand type(s) for -: 'list' and 'int'"),
    ('[] / 3',   "unsupported operand type(s) for /: 'list' and 'int'"),
    ('[] // 3',  "unsupported operand type(s) for //: 'list' and 'int'"),
    ('[] % 3',   "unsupported operand type(s) for %: 'list' and 'int'"),
    ('[] ** 3',  "unsupported operand type(s) for **: 'list' and 'int'"),
    ('[] @ 3',   "unsupported operand type(s) for @: 'list' and 'int'"),

    # unary operations for list
    ('+[]', "bad operand type for unary +: 'list'"),
    ('-[]', "bad operand type for unary -: 'list'"),
    ('~[]', "bad operand type for unary ~: 'list'"),

    # binary operations for set
    ('{1} - 3',   "unsupported operand type(s) for -: 'set' and 'int'"),
    ('{1} / 3',   "unsupported operand type(s) for /: 'set' and 'int'"),
    ('{1} // 3',  "unsupported operand type(s) for //: 'set' and 'int'"),
    ('{1} % 3',   "unsupported operand type(s) for %: 'set' and 'int'"),
    ('{1} ** 3',  "unsupported operand type(s) for **: 'set' and 'int'"),
    ('{1} @ 3',   "unsupported operand type(s) for @: 'set' and 'int'"),

    # unary operations for set
    ('+{1}', "bad operand type for unary +: 'set'"),
    ('-{1}', "bad operand type for unary -: 'set'"),
    ('~{1}', "bad operand type for unary ~: 'set'"),

])
def test_type_error(expr, err):
    with pytest.raises(TypeError):
        eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'