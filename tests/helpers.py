# project
from deal_solver import Theorem, Proof


def prove_f(text: str) -> Proof:
    theorems = list(Theorem.from_text(text))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    result = theorem.prove()
    print(repr(result))
    return result
