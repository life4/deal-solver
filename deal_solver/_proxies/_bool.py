import typing

# external
import z3

# app
from ._proxy import ProxySort
from ._registry import registry
from ._funcs import if_expr


if typing.TYPE_CHECKING:
    from ._int import IntSort


INT_BITS = 64


@registry.add
class BoolSort(ProxySort):
    type_name = 'bool'

    def __init__(self, expr) -> None:
        # assert z3.is_bool(expr), f'expected bool, given {type(expr)}'
        self.expr = expr

    @classmethod
    def sort(cls):
        return z3.BoolSort()

    @classmethod
    def val(cls, x) -> 'BoolSort':
        return cls(expr=z3.BoolVal(x))

    @property
    def as_bool(self) -> 'BoolSort':
        return self

    @property
    def as_int(self) -> 'IntSort':
        return if_expr(self, registry.int.val(1), registry.int.val(0))

    @property
    def as_float(self):
        return self.as_int.as_float
