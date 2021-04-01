# stdlib
import math
import operator
import typing
from sys import float_info

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import and_expr, switch, if_expr
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._int import IntSort
    from .._context import Context


FP_HANDLERS = {
    operator.__eq__: z3.fpEQ,
    operator.__ne__: z3.fpNEQ,
    operator.__gt__: z3.fpGT,
    operator.__ge__: z3.fpGEQ,
    operator.__lt__: z3.fpLT,
    operator.__le__: z3.fpLEQ,
}


@registry.add
class FloatSort(ProxySort):
    type_name = 'float'
    prefer_real = False

    def __new__(cls, expr=None):
        if cls is not FloatSort or expr is None:
            return super().__new__(cls)
        if z3.is_real(expr):
            return RealSort.__new__(RealSort)
        return FPSort.__new__(FPSort)

    @classmethod
    def sort(cls, ctx: z3.Context = None):
        if cls.prefer_real:
            return RealSort.sort(ctx=ctx)
        return FPSort.sort(ctx=ctx)

    @classmethod
    def val(cls, x: float, ctx: z3.Context = None) -> 'FloatSort':
        if not math.isfinite(x):
            return FPSort.val(x, ctx=ctx)
        if cls.prefer_real:
            return RealSort.val(x, ctx=ctx)
        return FPSort.val(x, ctx=ctx)

    @classmethod
    def wrap(cls, expr) -> 'FloatSort':
        if z3.is_real(expr):
            return RealSort(expr=expr)
        if z3.is_fp(expr):
            return FPSort(expr=expr)
        raise RuntimeError('unreachable')  # pragma: no cover

    @property
    def as_float(self) -> 'FloatSort':
        return self

    @property
    def is_real(self) -> bool:
        return z3.is_real(self.expr)

    @property
    def is_fp(self) -> bool:
        return z3.is_fp(self.expr)

    @property
    def as_str(self):
        raise UnsupportedError('cannot convert float to str')

    @property
    def is_nan(self) -> 'BoolSort':
        raise NotImplementedError

    def op_floor_div(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if self.is_real and other.is_real:
            return self.op_div(other, ctx=ctx).as_int.as_float

        if self.is_fp:
            other = other.as_fp
        zero = self.val(0.0)
        minus_one = self.val(-1.0)
        result = self.op_div(other, ctx=ctx).as_int.as_fp
        if other.is_fp:
            result = switch(
                (z3.Not(z3.fpIsInf(other.expr)), result),
                (and_expr(self.is_lt(zero, ctx=ctx), other.is_lt(zero, ctx=ctx)), zero),
                (and_expr(self.is_gt(zero, ctx=ctx), other.is_gt(zero, ctx=ctx)), zero),
                default=minus_one,
            )
        if self.is_fp:
            nan = z3.fpNaN(self.sort())
            result = if_expr(z3.fpIsInf(self.expr), nan, result)
            result = if_expr(z3.fpIsZero(self.expr), zero, result)

        return result

    def op_mul(self, other: 'ProxySort', ctx: 'Context') -> 'FloatSort':
        return self._math_op(other=other, handler=operator.__mul__, ctx=ctx)  # type: ignore


class RealSort(FloatSort):
    expr: z3.RatNumRef

    def __init__(self, expr) -> None:
        assert z3.is_real(expr), f'expected real, given {type(expr)}'
        self.expr = expr

    @classmethod
    def sort(cls, ctx: z3.Context = None):
        return z3.RealSort(ctx=ctx)

    @classmethod
    def val(cls, x: float, ctx: z3.Context = None):
        return cls(expr=z3.RealVal(x, ctx=ctx))

    @classmethod
    def _as_fp(cls, x):
        return z3.fpRealToFP(z3.RNE(), x, FPSort.sort())

    @property
    def as_real(self) -> 'RealSort':
        return self

    @property
    def as_fp(self) -> 'FPSort':
        return FPSort(expr=self._as_fp(self.expr))

    @property
    def as_int(self) -> 'IntSort':
        return registry.int(expr=z3.ToInt(self.expr))

    @property
    def as_bool(self) -> 'BoolSort':
        return registry.bool(expr=self.expr != z3.RealVal(0))

    @property
    def abs(self) -> 'RealSort':
        expr = z3.If(self.expr >= z3.RealVal(0), self.expr, -self.expr)
        return type(self)(expr=expr)

    @property
    def is_nan(self) -> 'BoolSort':
        return registry.bool.val(False)

    def _binary_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context'):
        if isinstance(other, registry.int):
            return handler(self.expr, other.as_real.expr)
        if not isinstance(other, FloatSort):
            msg = "unsupported operand type(s) for binary operation: '{}' and '{}'"
            msg = msg.format(self.type_name, other.type_name)
            ctx.add_exception(TypeError, msg)
            return self

        if other.is_real:
            return handler(self.expr, other.expr)
        if self.prefer_real:
            return handler(self.expr, other.as_real.expr)
        return handler(self.as_fp.expr, other.expr)

    def op_mod(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, FloatSort):
            return self.as_fp.op_mod(other.as_fp, ctx=ctx)
        if isinstance(other, registry.int):
            return self.as_fp.op_mod(other, ctx=ctx)
        return RealSort(expr=self.expr % other.expr)

    def op_div(self, other: ProxySort, ctx: 'Context') -> FloatSort:
        if isinstance(other, registry.int):
            return RealSort(expr=self.as_real.expr / other.as_real.expr)

        if other.is_real:
            return RealSort(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.expr / other.as_real.expr)
        return FPSort(expr=self.as_fp.expr / other.as_fp.expr)


class FPSort(FloatSort):

    def __init__(self, expr) -> None:
        assert z3.is_fp(expr), f'expected FPSort, given {type(expr)}'
        self.expr = expr

    @staticmethod
    def sort(ctx: z3.Context = None):
        # return z3.Float32()
        return z3.FPSort(ebits=float_info.dig, sbits=float_info.mant_dig, ctx=ctx)

    @classmethod
    def val(cls, x, ctx: z3.Context = None):
        return FPSort(expr=z3.FPVal(x, cls.sort(), ctx=ctx))

    @classmethod
    def _as_real(cls, x):
        return z3.fpToReal(x)

    @property
    def as_real(self) -> 'RealSort':
        return RealSort(expr=self._as_real(self.expr))

    @property
    def as_fp(self) -> 'FPSort':
        return self

    @property
    def as_int(self) -> 'IntSort':
        return registry.int(expr=z3.ToInt(self.as_real.expr))

    @property
    def as_bool(self) -> 'BoolSort':
        expr = self.expr != z3.FPVal(0, self.sort())
        return registry.bool(expr=expr)

    @property
    def is_nan(self) -> 'BoolSort':
        return registry.bool(expr=z3.fpIsNaN(self.expr))

    @property
    def abs(self) -> 'FPSort':
        return FPSort(expr=z3.fpAbs(self.expr))

    def _binary_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context'):
        real_handler = handler
        fp_handler = FP_HANDLERS.get(handler, handler)
        if isinstance(other, registry.int):
            return fp_handler(self.expr, other.as_fp.expr)
        if not isinstance(other, FloatSort):
            msg = "unsupported operand type(s) for binary operation: '{}' and '{}'"
            msg = msg.format(self.type_name, other.type_name)
            ctx.add_exception(TypeError, msg)
            return self

        if other.is_fp:
            return fp_handler(self.expr, other.expr)
        if self.prefer_real:
            return real_handler(self.as_real.expr, other.expr)
        return fp_handler(self.expr, other.as_fp.expr)

    def op_div(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, registry.int):
            return type(self)(expr=self.as_fp.expr / other.as_fp.expr)

        if other.is_fp:
            return type(self)(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.as_real.expr / other.as_real.expr)
        return type(self)(expr=self.expr / other.as_fp.expr)
