from deal_solver import Conclusion

from ..helpers import prove_f


def test_ok():
    theorem = prove_f("""
        @deal.post(lambda result: result == 0)
        def f(a: int) -> int:
            return a - a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_fail():
    theorem = prove_f("""
        @deal.post(lambda result: result != 13)
        def f(a: int) -> int:
            return a
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert theorem.example is not None
    assert dict(theorem.example)['a'] == 13


def test_fail_1_out_of_2():
    theorem = prove_f("""
        @deal.post(lambda result: result >= 0)
        @deal.post(lambda result: result != 9)
        def f(a: int) -> int:
            return a ** 2
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert theorem.example is not None
    assert dict(theorem.example)['a'] in (3, -3)


def test_pre_post_condition_name_conflict():
    theorem = prove_f("""
        @deal.post(lambda a: a > 10)
        @deal.pre(lambda a: a > 5)
        @deal.pre(lambda a: a < 10)
        def f(a: int) -> int:
            return a * 2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_condition_branching():
    theorem = prove_f("""
        @deal.post(lambda r: r >= 0)
        def f(a: int) -> int:
            if a > 0:
                return a
            else:
                return -a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_condition_branching_no_else():
    theorem = prove_f("""
        @deal.post(lambda r: r >= 0)
        def f(a: int) -> int:
            if a > 0:
                return a
            return -a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_condition_branching_many_branches():
    theorem = prove_f("""
        @deal.post(lambda r: r >= 0)
        def f(a: int) -> int:
            if a > 20:
                return a-20
            if a > 10:
                return a-10
            if a > 0:
                return a
            return -a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_cannot_resolve():
    theorem = prove_f("""
        @deal.post(unknown)
        @deal.post(lambda a: a >= 0)
        def f(a: int) -> int:
            return a * a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_ignore_empty():
    theorem = prove_f("""
        @deal.post(lambda: False)
        def f() -> int:
            assert True
    """)
    assert theorem.conclusion is Conclusion.OK
