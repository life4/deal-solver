import pytest

from deal_solver import Conclusion

from .helpers import prove_f


@pytest.mark.parametrize('xtype, xvalue', [
    (bool, True),
    (bool, False),
    (int, 12),
    (int, -12),
    (float, 12.1),
    (str, ''),
    (str, 'hello world'),
])
def test_model(xtype, xvalue):
    proof = prove_f(f"""
        def f(x: {xtype.__name__}):
            assert x != {repr(xvalue)}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    model = dict(proof.example)
    assert type(model['x']) is xtype
    assert model['x'] == xvalue


@pytest.mark.parametrize('xtype, xvalue', [
    ('list[int]', []),
    ('list[int]', [1]),
    ('list[int]', [1, 2]),
    ('list[str]', ['hi']),
    ('list[bool]', [True]),
    # ('tuple[int]', ()),
    ('list[float]', []),
    ('list[float]', [1.2]),
    ('set[int]', set()),
    ('set[int]', {1}),
    ('set[int]', {1, 2}),
    ('dict[int, int]', {1: 2}),
])
def test_model_generics(xtype, xvalue, prefer_real):
    proof = prove_f(f"""
        def f(x: {xtype}):
            assert x != {repr(xvalue)}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    model = dict(proof.example)
    assert model['x'] == xvalue


def test_model_str():
    proof = prove_f("""
        def f(b: bool, i: int):
            assert not b or i
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    assert proof.example
    assert str(proof.example) == 'b=True, i=0'


def test_model_bool():
    proof = prove_f("""
        def f():
            assert False
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    assert not proof.example
    assert str(proof.example) == ''


def test_model_skip_helpers():
    proof = prove_f("""
        def f(i: int):
            assert sum([3, i]) != 7
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    assert proof.example
    assert str(proof.example) == 'i=4'


def test_model_skip_helpers2():
    proof = prove_f("""
        def f(i: int):
            assert sum([x for x in [3, i]]) != 7
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.example is not None
    assert proof.example
    assert str(proof.example) == 'i=4'
