import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # compare
    '"ab" < "cd"',
    '"ab" <= "cd"',
    '"ab" <= "ab"',
    '"cd" > "ab"',
    '"cd" >= "ab"',
    '"ab" >= "ab"',
    '"a" > ""',
    '"ab" == "ab"',
    '"ab" != "cd"',
    '"" == ""',

    # operations
    '"ab" + "cd" == "abcd"',
    '"ab" + "cd" != "cdab"',
    '"bc" in "abcd"',
    # '"ab" * 3 == "ababab"',

    # getitem
    '"abc"[1] == "b"',

    # string functions
    'min("ab", "cd") == "ab"',
    'min("cd", "ab") == "ab"',
    'max("ab", "cd") == "cd"',
    'max("cd", "ab") == "cd"',
    'len("abcd") == 4',
    'len("") == 0',
    'str("abc") == "abc"',
    # 'float("12.3") == 12.3',
    'ord("a") == 97',
    'ord(".") == 46',
    'int("12") == 12',
    'bool("12") == True',
    'bool("") == False',
    'str(12) == "12"',

    # methods
    '"abcd".startswith("ab")',
    '"abcd".endswith("cd")',
    '"abcbcd".index("bc") == 1',
    '"abcbcd".index("bc", 2) == 3',
    '"abcbcd".find("bc") == 1',
    '"abcbcd".find("bc", 2) == 3',
    '"abcbcd".find("bc", 4) == -1',
    '"abcbcd".find("bd") == -1',
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


@pytest.mark.parametrize('check, exc, msg', [
    ('ord(1)',      TypeError, 'ord() expected string of length 1, but int found'),
])
def test_exceptions(check: str, exc, msg) -> None:
    with pytest.raises(exc):
        assert eval(check, dict(a='a', e=''))
    text = """
        def f():
            a = 'a'
            e = ''
            {}
    """
    text = text.format(check)
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.FAIL
    assert proof.description.startswith(exc.__name__)
    if msg:
        assert proof.description == f'{exc.__name__}: {msg}'
