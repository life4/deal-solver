# stdlib
import typing

# external
import z3

# app
from ._funcs import if_expr, unwrap, wrap
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._float import FloatSort, RealSort
    from ._str import StrSort
    from .._context import Context


INT_BITS = 64


@registry.add
class IntSort(ProxySort):
    type_name = 'int'

    def __init__(self, expr) -> None:
        assert z3.is_int(expr), f'expected int, given {type(expr)}'
        self.expr = expr

    @classmethod
    def sort(cls) -> z3.IntSort:
        return z3.IntSort()

    @classmethod
    def val(cls, x: int) -> 'IntSort':
        return cls(expr=z3.IntVal(x))

    @property
    def as_int(self) -> 'IntSort':
        return self

    @property
    def as_float(self) -> 'RealSort':
        # TODO: int to fp?
        return self.as_real

    @property
    def as_real(self) -> 'RealSort':
        return wrap(z3.ToReal(self.expr)).as_real

    @property
    def as_fp(self):
        expr = z3.ToReal(self.expr)
        return wrap(expr).as_fp

    @property
    def as_str(self) -> 'StrSort':
        return registry.str(expr=z3.IntToStr(self.expr))

    @property
    def as_bool(self) -> 'BoolSort':
        return registry.bool(expr=self.expr != z3.IntVal(0))

    @property
    def abs(self) -> 'IntSort':
        expr = z3.If(self.expr >= z3.IntVal(0), self.expr, -self.expr)
        return type(self)(expr=expr)

    def _math_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context') -> ProxySort:
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.as_int
        result = super()._math_op(other=other, handler=handler, ctx=ctx)
        if as_float:
            return result.as_float
        return result

    def op_div(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        real = z3.ToReal(self.expr)
        if isinstance(other, IntSort):
            return registry.float(expr=real / other.as_real.expr)
        if not isinstance(other, registry.float):
            self._bad_bin_op(other, op='/', ctx=ctx)
            return self.as_float
        if other.is_real:
            expr = real / other.as_real.expr
        else:
            expr = self.as_fp.expr / other.as_fp.expr
        return registry.float(expr=expr)

    def op_floor_div(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.as_int
        zero = self.val(0).expr
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr / other.expr,
            val_else=-self.expr / -other.expr,
        )
        if as_float:
            return result.as_float
        return result

    def op_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.as_int
        zero = self.val(0).expr
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr % other.expr,
            val_else=-(-self.expr % -other.expr),
        )
        if as_float:
            return result.as_float
        return result

    def as_inverted(self, ctx: 'Context') -> 'IntSort':
        expr = z3.BV2Int(~z3.Int2BV(self.expr, INT_BITS))
        zero = z3.IntVal(0)
        modulo = z3.IntVal(2 ** INT_BITS)
        expr = z3.If(self.expr >= zero, expr - modulo, expr)
        return type(self)(expr=expr)

    def _bitwise_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'IntSort':
        expr = z3.BV2Int(handler(
            z3.Int2BV(self.expr, INT_BITS),
            z3.Int2BV(unwrap(other), INT_BITS),
        ))
        return type(self)(expr=expr)
