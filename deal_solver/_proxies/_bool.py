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
    from .._context import Context
    from ._float import FloatSort, FPSort, RealSort
    from ._int import IntSort


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

    @property
    def as_real(self) -> 'RealSort':
        return self.as_int.as_real

    @property
    def as_fp(self) -> 'FPSort':
        return self.as_int.as_fp

    def _math_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context') -> ProxySort:
        return self.as_int._math_op(other=other, handler=handler, ctx=ctx)

    def op_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        return self.as_int.op_add(other, ctx=ctx)

    def op_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='%', ctx=ctx)
        return self.as_int.op_mod(other, ctx=ctx)

    def op_sub(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='-', ctx=ctx)
        return self.as_int.op_sub(other, ctx=ctx)

    def op_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='*', ctx=ctx)
        return self.as_int.op_mul(other, ctx=ctx)

    def op_div(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='/', ctx=ctx)
        return self.as_int.op_div(other, ctx=ctx)

    def op_floor_div(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='//', ctx=ctx)
        return self.as_int.op_floor_div(other, ctx=ctx)

    def as_negative(self, ctx: 'Context') -> 'ProxySort':
        return self.as_int.as_negative(ctx=ctx)

    def as_positive(self, ctx: 'Context') -> 'ProxySort':
        return self.as_int.as_positive(ctx=ctx)

    def as_inverted(self, ctx: 'Context') -> 'ProxySort':
        return self.as_int.as_inverted(ctx=ctx)
