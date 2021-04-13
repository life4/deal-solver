# stdlib
import math

# external
import hypothesis
import hypothesis.strategies
import pytest
from z3 import Z3Exception

# project
from deal_solver import Conclusion
from deal_solver._proxies import FloatSort

# app
from .helpers import prove_f


@pytest.mark.parametrize('check', [
    # logic
    'True',
    'not False',
    'True and True',
    'True or True',
    'False or True',
    'True or False',

    # math for int
    '13 == 13',
    '+12 == 12',
    '12 == --12',
    '-13 == -13',
    '+13 == --13',
    '3 + 6 == 9',
    '7 - 4 == 3',
    '7 * 4 == 28',
    '12 / 5 == 2.4',
    '13 // 5 == 2',
    '-13 // 5 == -3',
    '13 // -5 == -3',
    '13 % 5 == 3',
    '-5 % 2 == 1',
    '-1 % 3 == 2',
    '1 % -3 == -2',
    '5 % -2 == -1',
    '2 ** 3 == 8',

    # bitwise math for int
    '2 | 4 == 6',
    '3 & 6 == 2',
    '3 ^ 6 == 5',
    '6 << 1 == 12',
    '6 >> 1 == 3',
    '~3 == -4',
    '~-6 == 5',
    '~0 == -1',

    # math for float
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
    '2.7 > 1.4',
    '1.4 < 2.7',
    '2.7 == 2.7',
    'float("nan") != float("nan")',
    'float("inf") == float("inf")',
    '-0.0 == +0.0',

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

    # strings
    '"ab" < "cd"',
    '"ab" == "ab"',
    '"ab" != "cd"',
    '"ab" + "cd" == "abcd"',
    '"ab" + "cd" != "cdab"',
    '"bc" in "abcd"',
    # '"ab" * 3 == "ababab"',
    '"abc"[1] == "b"',

    # int functions
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

    # int methods
    '(12).conjugate() == 12',
    '(12).real == 12',
    '(12).numerator == 12',
    '(12).denominator == 1',
    '(12).imag == 0',

    # string functions
    'min("ab", "cd") == "ab"',
    'min("cd", "ab") == "ab"',
    'max("ab", "cd") == "cd"',
    'max("cd", "ab") == "cd"',
    'len("abcd") == 4',
    'str("abc") == "abc"',
    # 'float("12.3") == 12.3',
    'ord("a") == 97',
    'ord(".") == 46',

    # string methods
    '"abcd".startswith("ab")',
    '"abcd".endswith("cd")',
    '"abcbcd".index("bc") == 1',
    '"abcbcd".index("bc", 2) == 3',
    '"abcbcd".find("bc") == 1',
    '"abcbcd".find("bc", 2) == 3',
    '"abcbcd".find("bc", 4) == -1',
    '"abcbcd".find("bd") == -1',

    # float functions
    'bool(2.1) == True',
    'bool(0.0) == False',
    'int(4.2) == 4',
    'float(4.2) == 4.2',
    'float(10 / 2) == 5.0',
    'float("Inf") > 10000',
    'abs(-4.2) == 4.2',
    # 'str(4.2) == "4.2"',

    # float methods
    '(12.1).conjugate() == 12.1',
    '(12.1).real == 12.1',
    '(12.1).imag == 0',
    '(12.1).is_integer() == False',
    '(12.0).is_integer() == True',

    # bool functions
    'int(True) == 1',
    'int(False) == 0',
    'float(True) == 1.0',
    'float(False) == 0.0',
    'bool(True)',
    'not bool(False)',

    # list
    '[1, 2, 3] == [1, 2, 3]',
    '[1, 2, 3] != [1, 2, 3, 3]',
    '10 in [3, 6, 10, 17]',
    '11 not in [3, 6, 10, 17]',
    'not "" in [3]',
    '[4, 5, 6][1] == 5',
    '[4, 5, 6, 7, 8][2:4] == [6, 7]',
    '[4, 5, 6, 7, 8][2:] == [6, 7, 8]',
    '[4, 5, 6, 7, 8][:4] == [4, 5, 6, 7]',
    '[1, 2, 3][:] == [1, 2, 3]',
    '[1] + [2] == [1, 2]',
    '[1, 2] + [3, 4] == [1, 2, 3, 4]',
    '[] + [] == []',
    # '[1] * 3 == [1, 1, 1]',
    '([] + [True] + [False])[0] == True',

    # list methods
    '[7, 8, 8, 9].index(8) == 1',
    '[7, 8, 8, 9].index(8, 2) == 2',
    '[1, 2, 4, 6, 5, 6].count(6) == 2',
    '[1, 1, 1].count(1) == 3',
    '[1, 1, 1].count(2) == 0',
    '[].count(2) == 0',
    '[1, 2, 3].copy() == [1, 2, 3]',

    # list functions
    'len([7, 9, 9, 9, 11]) == 5',
    'min([7, 3, 5]) == 3',
    'max([3, 7, 5]) == 7',
    'sum([3, 7, 5]) == 15',
    'sum([sum([3, 7]), 5]) == 15',

    # set
    '{1, 2, 3} == {1, 2, 3}',
    '{1, 2, 3} != {1, 2, 3, 4}',
    '{1, 2, 3} == {3, 1, 2}',
    '{1, 2, 3} == {3, 2, 1, 1, 2}',
    # 'len({7, 9, 9, 9, 11}) == 3',
    '10 in {3, 6, 10, 17}',
    '{1, 2} | {2, 3} == {1, 2, 3}',
    '{1, 2}.union({2, 3}) == {1, 2, 3}',
    '{1, 2} & {2, 3} == {2}',
    '{1, 2}.intersection({2, 3}) == {2}',
    '{1, 2} ^ {2, 3} == {1, 3}',
    '{1, 2}.symmetric_difference({2, 3}) == {1, 3}',
    '{1, 2}.difference({2, 3}) == {1}',
    '{1, 2}.issubset({1, 2, 3})',
    'not {1, 2, 3}.issubset({1, 2})',
    '{1, 2, 3}.issuperset({1, 2})',
    'not {1, 2}.issuperset({1, 2, 3})',
    '{1, 2}.isdisjoint({3, 4})',
    'not {1, 2}.isdisjoint({2, 3})',

    # set methods
    '{1, 2}.copy() == {1, 2}',

    # tuple
    '(1, 2) == (1, 2)',
    '(1, 2) != (2, 1)',
    '(1, 2) != (2, 1)',
    '(1, 2) + (3,) == (1, 2, 3)',
    '(1, 2) + () == (1, 2)',
    '() + () == ()',
    '()[:3] == ()',
    '2 in (1, 2, 3)',
    '4 not in (1, 2, 3)',

    # other expressions
    'True if True else False',
    'False if False else True',

    # empty sequences
    # 'len(set()) == 0',
    'len([]) == 0',
    'len("") == 0',
    'set() == set()',
    '[] == []',
    '[] + [] == [] + [] + []',
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
    'not []',
    '[1, 2]',

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
