# external
import pytest

# project
from deal_solver import Conclusion

# app
from .helpers import prove_f


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
])
def test_math_module(check: str) -> None:
    text = """
        import math

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    'random.randint(1, 1) == 1',
    'random.randint(5, 9) > 4',
    'random.randint(5, 9) < 10',

    'random.randrange(5, 9) < 9',

    'random.choice([1]) == 1',
    'random.choice([1, 1]) == 1',
    'random.choice([1, 2, 3]) < 4',
    'random.choice([1, 2, 3]) > 0',

    # 'random.random() > -.1',
    # 'random.random() < 1.1',
])
def test_random_module(check: str) -> None:
    text = """
        import random

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    'os.path.join("ab", "cd") == "ab/cd"',
])
def test_os_path_module(check: str) -> None:
    text = """
        import os.path

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    # empty
    're.fullmatch("", "")',
    'not re.fullmatch("", "a")',

    # exact match
    're.fullmatch("ab", "ab")',
    'not re.fullmatch("ab", "a")',
    'not re.fullmatch("ab", "b")',
    'not re.fullmatch("a", "ab")',
    'not re.fullmatch("b", "ab")',

    # dot
    r're.fullmatch(".", "a")',
    r'not re.fullmatch(".", "aa")',
    r'not re.fullmatch(".", "\n")',

    # or
    're.fullmatch("a|b", "a")',
    're.fullmatch("a|b", "b")',
    'not re.fullmatch("a|b", "c")',
    'not re.fullmatch("a|b", "ab")',

    # digit
    r're.fullmatch(r"\d", "1")',
    r'not re.fullmatch(r"\d", "d")',

    # not digit
    r'not re.fullmatch(r"\D", "1")',
    r're.fullmatch(r"\D", "d")',

    # whitespace
    r're.fullmatch(r"\s", " ")',
    r're.fullmatch(r"\s", "	")',
    r'not re.fullmatch(r"\s", "s")',

    # newline
    r're.fullmatch(r"\n", "\n")',
    r'not re.fullmatch(r"\n", " ")',

    # letter
    r're.fullmatch(r"\w", "a")',
    r're.fullmatch(r"\w", "g")',
    r're.fullmatch(r"\w", "z")',
    r're.fullmatch(r"\w", "A")',
    r're.fullmatch(r"\w", "G")',
    r're.fullmatch(r"\w", "Z")',
    r'not re.fullmatch(r"\w", " ")',
    r'not re.fullmatch(r"\w", "?")',

    # range
    're.fullmatch(r"[a-c]", "a")',
    're.fullmatch(r"[a-c]", "b")',
    're.fullmatch(r"[a-c]", "c")',
    'not re.fullmatch(r"[a-c]", "d")',
    'not re.fullmatch(r"[a-c]", "aa")',

    # not a literal
    're.fullmatch(r"[^a]", "b")',
    'not re.fullmatch(r"[^a]", "a")',
    'not re.fullmatch(r"[^a]", "ab")',
    'not re.fullmatch(r"[^a]", "bc")',

    # re.match
    're.match("[ab]", "a")',
    're.match("[ab]", "ac")',
    'not re.match("[ab]", "c")',

    # re.Pattern.fullmatch
    're.compile("[ab]").fullmatch("a")',
    'not re.compile("[ab]").fullmatch("c")',

    # re.Pattern.match
    're.compile("[ab]").match("a")',
    're.compile("[ab]").match("ac")',
    'not re.compile("[ab]").match("c")',
])
def test_re_module(check: str) -> None:
    text = """
        import re

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
