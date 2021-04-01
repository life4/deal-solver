# project
import pytest
from deal_solver import Conclusion

# app
from .helpers import prove_f


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


@pytest.mark.parametrize('expr, err', [
    ('~"a"',      "bad operand type for unary ~: 'str'"),
    ('~3.14',     "bad operand type for unary ~: 'float'"),
    ('~[]',       "bad operand type for unary ~: 'list'"),
    ('3.1 | 4.2', "unsupported operand type(s) for bitwise operation: 'float' and 'float'"),
    ('4[0]',      "'int' object is not subscriptable"),
    ('4[:4]',     "'int' object is not subscriptable"),
    ('4.1[0]',    "'float' object is not subscriptable"),
    ('True[0]',   "'bool' object is not subscriptable"),
    ('4.1[:4]',   "'float' object is not subscriptable"),
])
def test_type_error(expr, err):
    proof = prove_f(f"""
        def f():
            {expr}
    """)
    assert proof.conclusion == Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'
