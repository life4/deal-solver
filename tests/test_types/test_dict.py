import pytest

from deal_solver import Conclusion, UnsupportedError

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    # contains
    '1 not in {}',
    '1 in {1: 2}',
    '3 in {1: 2, 3: 4}',
    '2 not in {1: 2}',
    '"" not in {1: 2}',

    # getitem
    '{1: 2}[1] == 2',

    # compare
    '{} == {}',
    '{1: 2} == {1: 2}',
    '{1: 2} != {2: 1}',
    '{1: 2} != {}',
    '{} != {1: 2}',
    '{"1": 2} != {1: 2}',
    '{1: "2"} != {1: 2}',

    # compare mismatching types
    '{1: 2} != {1}',
    '{1: 2} != (1,)',
    '{1: 2} != [1]',
    '{1: 2} != 1',
    '{1: 2} != 1.2',
    '{1: 2} != "1"',
    '{} != set()',
    '{} != []',
    '{} != 1',
    '{} != 1.2',
    '{} != ""',

    # methods
    '{1: 2}.get(1, 3) == 2',
    '{1: 2}.get(3, 4) == 4',
    '{}.get(1, 2) == 2',

    # functions
    'dict() == {}',
    'dict({1: 2}) == {1: 2}',
    'bool({}) == False',
    'bool({1: 2}) == True',
])
def test_asserts_ok(check: str) -> None:
    assert eval(check)
    text = """
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check, exc', [
    ('d[3]',        KeyError),
    ('e[1]',        KeyError),
    ('d[""]',       KeyError),
    ('e[""]',       KeyError),
    ('d.pop(3)',    KeyError),
    ('d.pop("")',   KeyError),
])
def test_exceptions(check: str, exc) -> None:
    with pytest.raises(exc):
        assert eval(check, dict(d={1: 2}, e={}))
    text = """
        def f():
            d = {{1: 2}}
            e = dict()
            {}
    """
    text = text.format(check)
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.FAIL
    assert proof.description.startswith(exc.__name__)


@pytest.mark.parametrize('check, msg', [
    ('{1: 2, "3": 4}', 'key has type str, expected int'),
    ('{1: 2, 3: "4"}', 'value has type str, expected int'),

    ('{1: 2}.items()', 'unsupported attribute for type dict'),
    ('{1: 2}.values()', 'unsupported attribute for type dict'),
    ('{1: 2}.update({3: 4})', 'unsupported attribute for type dict'),
])
def test_unsupported(check: str, msg) -> None:
    eval(check)
    text = """
        def f():
            {}
    """
    text = text.format(check)
    proof = prove_f(text)
    assert proof.conclusion == Conclusion.SKIP
    assert type(proof.error) is UnsupportedError
    assert str(proof.error) == msg


def test_dict_clear():
    theorem = prove_f("""
        def f():
            a = {1: 2, 3: 4}
            a.clear()
            a[1]
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert str(theorem.description) == 'KeyError'


def test_dict_clear_empty():
    theorem = prove_f("""
        def f():
            a = {}
            a.clear()
            assert a == {}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_pop():
    theorem = prove_f("""
        def f():
            a = {1: 2, 3: 4}
            r = a.pop(3)
            assert r == 4
            assert a == {1: 2}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_copy():
    theorem = prove_f("""
        def f():
            a = {1: 2, 3: 4}
            b = a.copy()
            a.pop(3)
            assert b == {1: 2, 3: 4}
    """)
    assert theorem.conclusion is Conclusion.OK


def test_setitem():
    theorem = prove_f("""
        def f():
            a = {1: 2}
            a[3] = 4
            assert a == {1: 2, 3: 4}
    """)
    assert theorem.conclusion is Conclusion.OK
