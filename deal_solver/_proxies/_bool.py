import typing

# external
import z3

# app
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    from ._int import IntSort


INT_BITS = 64


@registry.add
class BoolSort(ProxySort):
    type_name = 'bool'

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
        cls = registry.int
        expr = z3.If(self.expr, cls.val(1), cls.val(0))
        return cls(expr=expr)

    @property
    def as_float(self):
        return self.as_int.as_float
