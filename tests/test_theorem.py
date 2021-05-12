# external
import pytest

# project
from deal_solver import Theorem

# app
from .helpers import prove_f


def test_extract_function():
    text = """
        def f():
            return 13
    """
    theorems = list(Theorem.from_text(text))
    assert len(theorems) == 1
    assert theorems[-1].name == 'f'


def test_extract_staticmethod():
    text = """
        class A:
            @staticmethod
            def f():
                return 13
    """
    theorems = list(Theorem.from_text(text))
    assert len(theorems) == 1
    assert theorems[-1].name == 'f'


def test_ignore_method():
    text = """
        class A:
            def f(self):
                return 13
    """
    theorems = list(Theorem.from_text(text))
    assert len(theorems) == 0


@pytest.mark.parametrize('expr, expected', [
    ('def f(): 13', 'nothing to prove'),
    ('def f(): assert 1', 'assertion'),
    ('def f(): raise ValueError', 'ValueError'),
    ('def f(): raise ValueError("hello")', 'ValueError'),
    ('def f(x: int): assert x != 12', 'assertion. Example: x=12.'),
    ('def f(): zz', 'failed to interpret statement (cannot resolve name zz)'),
])
def test_proof_str(expr, expected):
    proof = prove_f(expr)
    assert str(proof) == expected
