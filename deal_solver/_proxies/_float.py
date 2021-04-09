# stdlib
import math
import operator
import typing
from sys import float_info

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import and_expr, if_expr, switch
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort


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
    methods = ProxySort.methods.copy()

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

    @methods.add(name='__float__')
    def m_float(self, ctx: 'Context') -> 'FloatSort':
        return self

    @property
    def is_real(self) -> bool:
        return z3.is_real(self.expr)

    @property
    def is_fp(self) -> bool:
        return z3.is_fp(self.expr)

    @methods.add(name='__str__')
    def m_str(self, ctx: 'Context'):
        raise UnsupportedError('cannot convert float to str')

    @property
    def is_nan(self) -> 'BoolSort':
        raise NotImplementedError

    def m_pow(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='** or pow()', ctx=ctx)
        return self._math_op(other=other, handler=operator.__pow__, ctx=ctx)

    def m_floordiv(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.float, registry.int)):
            return self._bad_bin_op(other, op='//', ctx=ctx)
        if self.is_real and other.is_real:
            return self.m_truediv(other, ctx=ctx).m_int(ctx=ctx).m_float(ctx=ctx)

        if self.is_fp:
            other = other.m_fp(ctx=ctx)
        zero = self.val(0.0)
        minus_one = self.val(-1.0)
        result = self.m_truediv(other, ctx=ctx).m_int(ctx=ctx).m_fp(ctx=ctx)
        if other.is_fp:
            result = switch(
                (z3.Not(z3.fpIsInf(other.expr)), result),
                (and_expr(self.m_lt(zero, ctx=ctx), other.m_lt(zero, ctx=ctx), ctx=ctx), zero),
                (and_expr(self.m_gt(zero, ctx=ctx), other.m_gt(zero, ctx=ctx), ctx=ctx), zero),
                default=minus_one,
                ctx=ctx,
            )
        if self.is_fp:
            nan = z3.fpNaN(FPSort.sort())
            result = if_expr(z3.fpIsInf(self.expr), nan, result, ctx=ctx)
            result = if_expr(z3.fpIsZero(self.expr), zero, result, ctx=ctx)

        return result

    def m_mul(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, (registry.str, registry.list)):
            msg = "can't multiply sequence by non-int of type '{}'"
            msg = msg.format(self.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.float, registry.int)):
            return self._bad_bin_op(other, op='*', ctx=ctx)
        return self._math_op(other=other, handler=operator.__mul__, ctx=ctx)  # type: ignore

    def m_add(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.float, registry.int)):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    def m_sub(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.float, registry.int)):
            return self._bad_bin_op(other, op='-', ctx=ctx)
        return self._math_op(other=other, handler=operator.__sub__, ctx=ctx)

    def m_mod(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.float, registry.int)):
            return self._bad_bin_op(other, op='%', ctx=ctx)
        return self._math_op(other=other, handler=operator.__mod__, ctx=ctx)


class RealSort(FloatSort):
    methods = FloatSort.methods.copy()
    expr: z3.RatNumRef

    def __init__(self, expr) -> None:
        assert z3.is_real(expr), f'expected real, given {type(expr)}'
        self.expr = expr

    @classmethod
    def val(cls, x: float, ctx: z3.Context = None):
        return cls(expr=z3.RealVal(x, ctx=ctx))

    @classmethod
    def _as_fp(cls, x):
        return z3.fpRealToFP(z3.RNE(), x, FPSort.sort())

    def m_real(self, ctx: 'Context') -> 'RealSort':
        return self

    def m_fp(self, ctx: 'Context') -> 'FPSort':
        return FPSort(expr=self._as_fp(self.expr))

    @methods.add(name='__int__')
    def m_int(self, ctx: 'Context') -> 'IntSort':
        return registry.int(expr=z3.ToInt(self.expr))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
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
            return handler(self.expr, other.m_real(ctx=ctx).expr)
        if other.is_real:
            return handler(self.expr, other.expr)
        if self.prefer_real:
            return handler(self.expr, other.m_real(ctx=ctx).expr)
        return handler(self.m_fp(ctx=ctx).expr, other.expr)

    def m_mod(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, registry.float):
            return self.m_fp(ctx=ctx).m_mod(other.m_fp(ctx=ctx), ctx=ctx)
        if isinstance(other, registry.int):
            return self.m_fp(ctx=ctx).m_mod(other, ctx=ctx)
        return self._bad_bin_op(other, op='%', ctx=ctx)

    def m_truediv(self, other: ProxySort, ctx: 'Context') -> FloatSort:
        if isinstance(other, (registry.int, registry.bool)):
            return RealSort(expr=self.m_real(ctx=ctx).expr / other.m_real(ctx=ctx).expr)
        if not isinstance(other, registry.float):
            return self._bad_bin_op(other, op='/', ctx=ctx)

        if other.is_real:
            return RealSort(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.expr / other.m_real(ctx=ctx).expr)
        return FPSort(expr=self.m_fp(ctx=ctx).expr / other.m_fp(ctx=ctx).expr)


class FPSort(FloatSort):
    methods = FloatSort.methods.copy()

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

    def m_real(self, ctx: 'Context') -> 'RealSort':
        return RealSort(expr=self._as_real(self.expr))

    def m_fp(self, ctx: 'Context') -> 'FPSort':
        return self

    @methods.add(name='__int__')
    def m_int(self, ctx: 'Context') -> 'IntSort':
        return registry.int(expr=z3.ToInt(self.m_real(ctx=ctx).expr))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
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
        if isinstance(other, (registry.int, registry.bool)):
            return fp_handler(self.expr, other.m_fp(ctx=ctx).expr)

        if other.is_fp:
            return fp_handler(self.expr, other.expr)
        if self.prefer_real:
            return real_handler(self.m_real(ctx=ctx).expr, other.expr)
        return fp_handler(self.expr, other.m_fp(ctx=ctx).expr)

    def m_truediv(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, (registry.int, registry.bool)):
            return type(self)(expr=self.m_fp(ctx=ctx).expr / other.m_fp(ctx=ctx).expr)
        if not isinstance(other, registry.float):
            return self._bad_bin_op(other, op='/', ctx=ctx)

        if other.is_fp:
            return type(self)(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.m_real(ctx=ctx).expr / other.m_real(ctx=ctx).expr)
        return type(self)(expr=self.expr / other.m_fp(ctx=ctx).expr)
