# stdlib
import typing

# external
import z3

# app
from ._funcs import if_expr
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from ._int import FloatSort, IntSort


INT_BITS = 64


@registry.add
class BoolSort(ProxySort):
    type_name = 'bool'

    def __init__(self, expr) -> None:
        assert z3.is_bool(expr) or z3.is_seq(expr), f'expected bool, given {type(expr)}'
        self.expr = expr

    @classmethod
    def sort(cls) -> z3.BoolSortRef:
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
    def as_float(self) -> 'FloatSort':
        return self.as_int.as_float
