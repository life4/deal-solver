
import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    'os.path.join("ab", "cd") == "ab/cd"',
])
def test_os_path_module(check: str) -> None:
    text = """
        import os.path

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('expr, err', [
    ('os.path.join("", 123)', 'expected str, bytes or os.PathLike object, not int'),
    ('os.path.join(123, "")', 'expected str, bytes or os.PathLike object, not int'),
])
def test_os_path_module_type_error(expr: str, err: str) -> None:
    text = """
        import os

        def f():
            assert {}
    """
    text = text.format(expr)
    proof = prove_f(text)
    assert proof.conclusion is Conclusion.FAIL
    assert proof.description == f'TypeError: {err}'
