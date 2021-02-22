# project
from deal_solver import Conclusion, Theorem


def prove_f(text: str) -> Theorem:
    theorems = list(Theorem.from_text(text))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    assert theorem.result is None
    theorem.prove()
    assert theorem.result is not None
    if theorem.result.conclusion != Conclusion.OK:
        print(repr(theorem.result))
    return theorem
