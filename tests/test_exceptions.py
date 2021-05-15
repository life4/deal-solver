import re

import pytest

from deal_solver import Conclusion

from .helpers import prove_f


@pytest.mark.parametrize('expr, exc, err', [
    ('[][0]',       IndexError, 'list index out of range'),
    ('[4][1]',      IndexError, 'list index out of range'),
])
def test_type_error__table(prefer_real, expr, exc, err):
    with pytest.raises(exc, match=re.escape(err)):
        eval(expr)
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description == f'{exc.__name__}: {err}'


def test_ok():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ValueError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_fail():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ZeroDivisionError
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_instance_ok():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ValueError("hi")
    """)
    assert theorem.conclusion is Conclusion.OK


def test_instance_fail():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ZeroDivisionError("hi")
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_subclasses_builtin():
    theorem = prove_f("""
        @deal.raises(LookupError)
        def f():
            raise IndexError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_subclasses_custom_class():
    theorem = prove_f("""
        class Custom(IndexError):
            pass

        @deal.raises(LookupError)
        def f():
            raise Custom
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_then_ok():
    theorem = prove_f("""
        def f():
            if False:
                raise ValueError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_then_fail():
    theorem = prove_f("""
        def f():
            if True:
                raise ValueError
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_if_else_ok():
    theorem = prove_f("""
        def f():
            if True:
                pass
            else:
                raise ValueError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_else_fail():
    theorem = prove_f("""
        def f():
            if False:
                pass
            else:
                raise ValueError
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_raise_from_first():
    theorem = prove_f("""
        @deal.raises(ZeroDivisionError)
        def f():
            raise ValueError from ZeroDivisionError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_raise_from_second():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            raise ValueError from ZeroDivisionError
    """)
    assert theorem.conclusion is Conclusion.OK


def test_raise_shadow_assert():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            if True:
                raise ValueError
            assert False
    """)
    assert theorem.conclusion is Conclusion.OK


def test_raise_do_not_shadow_assert():
    theorem = prove_f("""
        @deal.raises(ValueError)
        def f():
            if False:
                raise ValueError
            assert False
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_return_shadows_raise():
    theorem = prove_f("""
        def f():
            if True:
                return 123
            raise Exception
    """)
    assert theorem.conclusion is Conclusion.OK


def test_return_not_shadow_raise():
    theorem = prove_f("""
        def f():
            if False:
                return 123
            raise Exception
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_raise_shadow_return():
    theorem = prove_f("""
        def f():
            if True:
                raise Exception
            return 123
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_raise_not_shadow_return():
    theorem = prove_f("""
        def f():
            if False:
                raise Exception
            return 123
    """)
    assert theorem.conclusion is Conclusion.OK
