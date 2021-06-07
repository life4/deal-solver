import astroid
import pytest

from deal_solver._ast import get_full_name, get_name


@pytest.mark.parametrize('given, expected', [
    ('hello',       'hello'),
    ('hello.world', 'hello.world'),
    ('[].hello',    None),
    ('[]',          None),
])
def test_get_name(given, expected):
    actual = get_name(astroid.extract_node(given))
    assert actual == expected


@pytest.mark.parametrize('given, expected', [
    (
        """
            def fn(): pass
            fn
        """,
        ('', 'fn'),
    ),
    (
        """
            class Ex: pass
            Ex
        """,
        ('', 'Ex'),
    ),
    (
        """
            def f1():
                def f2(): pass
                return f2
            f3 = f1()
            f3
        """,
        ('', 'f1.f2'),
    ),
])
def test_get_full_name(given, expected):
    node = astroid.extract_node(given).inferred()[0]
    actual = get_full_name(node)
    assert actual == expected
