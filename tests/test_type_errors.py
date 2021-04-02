import pytest
import hypothesis
import hypothesis.strategies

# project
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

    # binary operations for int
    ('4 / "a"',   "unsupported operand type(s) for /: 'int' and 'str'"),
    ('4 // "a"',  "unsupported operand type(s) for //: 'int' and 'str'"),
    ('4 % "a"',   "unsupported operand type(s) for %: 'int' and 'str'"),
    ('3 @ 3',     "unsupported operand type(s) for @: 'int' and 'int'"),
    ('3 + ""',    "unsupported operand type(s) for +: 'int' and 'str'"),
    ('3 - ""',    "unsupported operand type(s) for -: 'int' and 'str'"),
    ('3 * set()', "unsupported operand type(s) for *: 'int' and 'set'"),
    ('3 ** ""',   "unsupported operand type(s) for **: 'int' and 'str'"),

    # binary operations for float
    ('4.1 + []',  "unsupported operand type(s) for +: 'float' and 'list'"),
    ('4.1 - []',  "unsupported operand type(s) for -: 'float' and 'list'"),
    ('4.1 * []',  "unsupported operand type(s) for *: 'float' and 'list'"),
    ('4.1 ** []', "unsupported operand type(s) for **: 'float' and 'list'"),
    ('4.1 @ []',  "unsupported operand type(s) for @: 'float' and 'list'"),
    ('4.1 % []',  "unsupported operand type(s) for %: 'float' and 'list'"),
    ('4.1 / []',  "unsupported operand type(s) for /: 'float' and 'list'"),
    ('4.1 // []', "unsupported operand type(s) for //: 'float' and 'list'"),

    # binary operations for str
    ('"a" + 3',   "unsupported operand type(s) for +: 'str' and 'int'"),
    ('"" * ""',   "unsupported operand type(s) for *: 'str' and 'str'"),
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
    ('[] + ""',  'can only concatenate list (not "str") to list'),
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
    ('{1} + 3',   "unsupported operand type(s) for +: 'set' and 'int'"),
    ('{1} * 3',   "unsupported operand type(s) for *: 'set' and 'int'"),
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
def test_type_error__table(prefer_real, expr, err):
    with pytest.raises(TypeError):
        eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'


@hypothesis.settings(
    report_multiple_bugs=False,
    suppress_health_check=[
        hypothesis.HealthCheck.function_scoped_fixture,  # type: ignore
    ],
)
@hypothesis.given(
    left=hypothesis.strategies.sampled_from(['""', '[]', 'set()', '1', '3.4']),
    right=hypothesis.strategies.sampled_from(['""', '[]', 'set()', '1', '1.2', 'True']),
    op=hypothesis.strategies.sampled_from([
        '+', '-', '*', '**', '/', '//', '%',
    ]),
)
def test_type_error__fuzz(prefer_real: bool, left: str, op: str, right: str):
    expr = f'{left} {op} {right}'

    try:
        eval(expr)
    except TypeError:
        pass
    else:
        hypothesis.reject()
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description.startswith('TypeError')
