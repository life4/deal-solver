# project
from deal_solver import Theorem


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
