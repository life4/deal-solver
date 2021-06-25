
import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


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

    # not whitespace
    r're.fullmatch(r"\S", "s")',
    r'not re.fullmatch(r"\S", "ss")',
    r'not re.fullmatch(r"\S", " ")',
    r'not re.fullmatch(r"\S", "\n")',

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

    # not letter
    r're.fullmatch(r"\W", " ")',
    r're.fullmatch(r"\W", "?")',
    r'not re.fullmatch(r"\W", "abs")',
    r'not re.fullmatch(r"\W", "a")',
    r'not re.fullmatch(r"\W", "g")',
    r'not re.fullmatch(r"\W", "z")',
    r'not re.fullmatch(r"\W", "A")',
    r'not re.fullmatch(r"\W", "G")',
    r'not re.fullmatch(r"\W", "Z")',

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

    # question mark (zero or one)
    're.fullmatch("ab?", "a")',
    're.fullmatch("ab?", "ab")',
    'not re.fullmatch("ab?", "abb")',
    'not re.fullmatch("ab?", "b")',
    'not re.fullmatch("ab?", "abc")',

    # star (zero or more)
    're.fullmatch("ab*", "a")',
    're.fullmatch("ab*", "ab")',
    're.fullmatch("ab*", "abb")',
    'not re.fullmatch("ab*", "b")',
    'not re.fullmatch("ab*", "abc")',

    # plus (one or more)
    'not re.fullmatch("ab+", "a")',
    're.fullmatch("ab+", "ab")',
    're.fullmatch("ab+", "abb")',
    'not re.fullmatch("ab+", "b")',
    'not re.fullmatch("ab+", "abc")',

    # N or more
    'not re.fullmatch("ab{2,}", "a")',
    'not re.fullmatch("ab{2,}", "ab")',
    're.fullmatch("ab{2,}", "abb")',
    're.fullmatch("ab{2,}", "abbb")',
    'not re.fullmatch("ab{2,}", "b")',
    'not re.fullmatch("ab{2,}", "abc")',

    # range loop
    'not re.fullmatch("ab{2,4}", "a")',
    'not re.fullmatch("ab{2,4}", "ab")',
    're.fullmatch("ab{2,4}", "abb")',
    're.fullmatch("ab{2,4}", "abbb")',
    're.fullmatch("ab{2,4}", "abbbb")',
    'not re.fullmatch("ab{2,4}", "abbbbb")',
    'not re.fullmatch("ab{2,4}", "b")',
    'not re.fullmatch("ab{2,4}", "abc")',

    # subpattern
    're.fullmatch("a(bc)", "abc")',
    'not re.fullmatch("a(bc)", "a")',
    'not re.fullmatch("a(bc)", "ab")',
    'not re.fullmatch("a(bc)", "bc")',

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


@pytest.mark.parametrize('expr, err', [
    # ('re.fullmatch(123, "")', 'first argument must be string or compiled pattern'),
    ('re.fullmatch("", 123)', 'expected string or bytes-like object'),
    ('re.match("", 123)', 'expected string or bytes-like object'),
])
def test_re_module_type_error(expr: str, err: str) -> None:
    text = """
        import re

        def f():
            assert {}
    """
    text = text.format(expr)
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'


@pytest.mark.parametrize('pat', [
    'Isaac (?=Asimov)',
    '^hi$',
])
def test_unsupported(pat: str):
    proof = prove_f(f"""
        import re

        def f():
            re.compile('{pat}')
    """)
    assert proof.conclusion is Conclusion.SKIP
    assert str(proof.error) == 'cannot interpret regexp'
