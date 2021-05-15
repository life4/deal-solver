import pytest

from deal_solver import Conclusion

from .helpers import prove_f


@pytest.mark.parametrize('xtype, xvalue', [
    (bool, True),
    (bool, False),
    (int, 12),
    (int, -12),
    (float, 12.1),
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
