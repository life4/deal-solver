
import pytest

from deal_solver import Conclusion

from ..helpers import prove_f


@pytest.mark.parametrize('check', [
    'random.randint(1, 1) == 1',
    'random.randint(5, 9) > 4',
    'random.randint(5, 9) < 10',

    'random.randrange(5, 9) < 9',

    'random.choice([1]) == 1',
    'random.choice([1, 1]) == 1',
    'random.choice([1, 2, 3]) < 4',
    'random.choice([1, 2, 3]) > 0',

    # 'random.random() > -.1',
    # 'random.random() < 1.1',
])
def test_random_module(check: str) -> None:
    text = """
        import random

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
