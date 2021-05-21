import typing

import astroid

from deal_solver import Contract, Proof, Theorem
from deal_solver._ast import get_name


class TestTheorem(Theorem):
    @staticmethod
    def get_contracts(func: astroid.FunctionDef) -> typing.Iterator[Contract]:
        if not func.decorators:
            return
        for contract in func.decorators.nodes:
            name = get_name(contract.func)
            assert name
            yield Contract(
                name=name.split('.')[-1],
                args=contract.args,
            )


def prove_f(text: str, **kwargs) -> Proof:
    theorems = list(TestTheorem.from_text(text, **kwargs))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    proof = theorem.prove()
    print(repr(proof))
    return proof
