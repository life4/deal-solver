from deal_solver import Conclusion

from .helpers import prove_f


def test_custom_error_bad_parents():
    theorem = prove_f("""
        def func(): pass

        class CustomBase(IndexError):
            pass

        class Custom(CustomBase, func, object, sum, int.bit_length):
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


def test_ignore_invalid():
    theorem = prove_f("""
        @deal.raises(lambda:0)
        def f():
            assert True
    """)
    assert theorem.conclusion is Conclusion.OK
