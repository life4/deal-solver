# import pytest
from deal_solver import Conclusion

from .helpers import prove_f


def test_variable():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 13
            assert a != 14
            assert a == a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_variable_fail():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 15
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_reassign_var():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 13
            assert a != 15

            a = 15
            assert a != 13
            assert a == 15

            b = 11
            assert a != b
            a = 11
            assert a == b
    """)
    assert theorem.conclusion is Conclusion.OK


def test_ternary_if_expr():
    theorem = prove_f("""
        def f():
            a = 13 if True else 16
            assert a == 13

            a = 13 if False else 16
            assert a == 16
    """)
    assert theorem.conclusion is Conclusion.OK


def test_unary_minus():
    theorem = prove_f("""
        def f():
            a = 13
            assert -a == -13
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_single_arg():
    theorem = prove_f("""
        def f(a: int):
            assert a == a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_two_args():
    theorem = prove_f("""
        def f(a: int, b: int):
            assert a + b == b + a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_two_args_fail_for_some():
    theorem = prove_f("""
        def f(a: int, b: int):
            assert a != b
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_no_effect_statements():
    theorem = prove_f("""
        def f():
            print("hello")
            pass
    """)
    assert theorem.conclusion is Conclusion.OK


def test_multiple_assignment_targets():
    theorem = prove_f("""
        def f():
            a = b = 13
            assert a == 13
            assert b == 13
            assert a == b
    """)
    assert theorem.conclusion is Conclusion.OK
