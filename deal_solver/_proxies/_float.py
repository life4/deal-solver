import math
import operator
import typing
from sys import float_info

import z3

from .._exceptions import UnsupportedError
from ._funcs import and_expr, switch
from ._proxy import ProxySort
from ._registry import types
from ._type_factory import TypeFactory


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort


FP_HANDLERS = {
    operator.__gt__: z3.fpGT,
    operator.__ge__: z3.fpGEQ,
    operator.__lt__: z3.fpLT,
    operator.__le__: z3.fpLEQ,
}


@types.add
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
    def var(cls, *, name: str, ctx: z3.Context) -> 'FloatSort':
        expr = z3.Const(
            name=name,
            sort=cls.sort(ctx=ctx),
        )
        return cls(expr=expr)

    @property
    def factory(self) -> TypeFactory:
        cls = type(self)
        if self.is_real:
            default = z3.RealVal(.0, ctx=self.expr.ctx)
        else:
            default = z3.FPVal(.0, cls.sort(), ctx=self.expr.ctx)
        return TypeFactory(
            type=cls,
            default=type(self)(default),
            subtypes=(),
        )

    @classmethod
    def sort(cls, ctx: z3.Context = None) -> z3.SortRef:
        if cls.prefer_real:
            return RealSort.sort(ctx=ctx)
        return FPSort.sort(ctx=ctx)

    @classmethod
    def val(cls, x: float, ctx: 'Context' = None) -> 'FloatSort':
        if ctx is not None:
            ctx = ctx.z3_ctx
        if not math.isfinite(x):
            return FPSort.val(x, ctx=ctx)
        if cls.prefer_real:
            return RealSort.val(x, ctx=ctx)
        return FPSort.val(x, ctx=ctx)

    @methods.add(name='__float__')
    @methods.add(name='conjugate')
    @methods.add(name='real', prop=True)
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

    @methods.add(name='__pow__')
    def m_pow(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if not isinstance(other, (types.bool, types.int, types.float)):
            return self._bad_bin_op(other, op='** or pow()', ctx=ctx)
        raise UnsupportedError('cannot raise float in a power')

    @methods.add(name='__floordiv__')
    def m_floordiv(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (types.float, types.int)):
            return self._bad_bin_op(other, op='//', ctx=ctx)
        if self.is_real and other.is_real:
            return self.m_truediv(other, ctx=ctx).m_int(ctx=ctx).m_float(ctx=ctx)

        if self.is_fp:
            other = other.m_fp(ctx=ctx)
        zero = self.val(0.0)
        minus_one = self.val(-1.0)
        result: ProxySort
        result = self.m_truediv(other, ctx=ctx).m_int(ctx=ctx)
        if self.is_fp:
            result = result.m_fp(ctx=ctx)
        else:
            result = result.m_real(ctx=ctx)
        if other.is_fp:
            result = switch(
                (types.bool(z3.Not(z3.fpIsInf(other.expr))), result),
                (and_expr(self.m_lt(zero, ctx=ctx), other.m_lt(zero, ctx=ctx), ctx=ctx), zero),
                (and_expr(self.m_gt(zero, ctx=ctx), other.m_gt(zero, ctx=ctx), ctx=ctx), zero),
                default=minus_one,
                ctx=ctx,
            )
        if self.is_fp:
            nan = z3.fpNaN(FPSort.sort())
            result_expr = z3.If(z3.fpIsInf(self.expr), nan, result.expr, ctx=ctx)
            result_expr = z3.If(z3.fpIsZero(self.expr), zero.expr, result_expr, ctx=ctx)
            result = FPSort(result_expr)

        return result

    @methods.add(name='__mul__')
    def m_mul(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, (types.str, types.list)):
            msg = "can't multiply sequence by non-int of type '{}'"
            msg = msg.format(self.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (types.float, types.int)):
            return self._bad_bin_op(other, op='*', ctx=ctx)
        expr = self._binary_op(other=other, handler=operator.__mul__, ctx=ctx)
        return types.float(expr)

    @methods.add(name='__add__')
    def m_add(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (types.float, types.int)):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        expr = self._binary_op(other=other, handler=operator.__add__, ctx=ctx)
        return types.float(expr)

    @methods.add(name='__sub__')
    def m_sub(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (types.float, types.int)):
            return self._bad_bin_op(other, op='-', ctx=ctx)
        expr = self._binary_op(other=other, handler=operator.__sub__, ctx=ctx)
        return types.float(expr)

    @methods.add(name='imag', prop=True)
    def m_imag(self, ctx: 'Context') -> 'FloatSort':
        return self.val(0)

    @methods.add(name='is_integer')
    def m_is_integer(self, ctx: 'Context') -> 'BoolSort':
        return self.m_eq(self.m_int(ctx=ctx).m_float(ctx=ctx), ctx=ctx)

    @methods.add(name='as_integer_ratio')
    @methods.add(name='from_hex')
    @methods.add(name='hex')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        if isinstance(other, (types.int, types.bool, types.float)):
            if self.is_real:
                other = other.m_real(ctx=ctx)
            else:
                other = other.m_fp(ctx=ctx)
        if not isinstance(other, types.float):
            return types.bool.val(False, ctx=ctx)
        if self.is_real and other.is_real:
            expr = self.m_real(ctx=ctx).expr == other.m_real(ctx=ctx).expr
            return types.bool(expr=expr)
        expr = z3.fpEQ(
            self.m_fp(ctx=ctx).expr,
            other.m_fp(ctx=ctx).expr,
        )
        return types.bool(expr=expr)


class RealSort(FloatSort):
    methods = FloatSort.methods.copy()
    expr: z3.RatNumRef

    def __init__(self, expr) -> None:
        assert z3.is_real(expr), f'expected real, given {type(expr)}'
        self.expr = expr

    @staticmethod
    def sort(ctx: z3.Context = None):
        return z3.RealSort(ctx=ctx)

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
        return types.int(expr=z3.ToInt(self.expr))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        return types.bool(expr=self.expr != z3.RealVal(0))

    @methods.add(name='__abs__')
    def m_abs(self, ctx: 'Context') -> ProxySort:
        expr = z3.If(self.expr >= z3.RealVal(0), self.expr, -self.expr, ctx=ctx.z3_ctx)
        return type(self)(expr=expr)

    @property
    def is_nan(self) -> 'BoolSort':
        return types.bool.val(False)

    def _binary_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context'):
        if isinstance(other, (types.int, types.bool)):
            return handler(self.expr, other.m_real(ctx=ctx).expr)
        if other.is_real:
            return handler(self.expr, other.expr)
        if self.prefer_real:
            return handler(self.expr, other.m_real(ctx=ctx).expr)
        return handler(self.m_fp(ctx=ctx).expr, other.expr)

    @methods.add(name='__mod__')
    def m_mod(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if isinstance(other, types.float):
            return self.m_fp(ctx=ctx).m_mod(other.m_fp(ctx=ctx), ctx=ctx)
        if isinstance(other, types.int):
            return self.m_fp(ctx=ctx).m_mod(other, ctx=ctx)
        return self._bad_bin_op(other, op='%', ctx=ctx)

    @methods.add(name='__truediv__')
    def m_truediv(self, other: ProxySort, ctx: 'Context') -> FloatSort:
        if isinstance(other, (types.int, types.bool)):
            return RealSort(expr=self.m_real(ctx=ctx).expr / other.m_real(ctx=ctx).expr)
        if not isinstance(other, types.float):
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
        return types.int(expr=z3.ToInt(self.m_real(ctx=ctx).expr))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        expr = self.expr != z3.FPVal(0, self.sort())
        return types.bool(expr=expr)

    @property
    def is_nan(self) -> 'BoolSort':
        return types.bool(expr=z3.fpIsNaN(self.expr))

    @methods.add(name='__abs__')
    def m_abs(self, ctx: 'Context') -> ProxySort:
        return FPSort(expr=z3.fpAbs(self.expr, ctx=ctx.z3_ctx))

    def _binary_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context'):
        real_handler = handler
        fp_handler = FP_HANDLERS.get(handler, handler)
        if isinstance(other, (types.int, types.bool)):
            return fp_handler(self.expr, other.m_fp(ctx=ctx).expr)

        if other.is_fp:
            return fp_handler(self.expr, other.expr)
        if self.prefer_real:
            return real_handler(self.m_real(ctx=ctx).expr, other.expr)
        return fp_handler(self.expr, other.m_fp(ctx=ctx).expr)

    @methods.add(name='__truediv__')
    def m_truediv(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        if isinstance(other, (types.int, types.bool)):
            return type(self)(expr=self.m_fp(ctx=ctx).expr / other.m_fp(ctx=ctx).expr)
        if not isinstance(other, types.float):
            return self._bad_bin_op(other, op='/', ctx=ctx)

        if other.is_fp:
            return type(self)(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.m_real(ctx=ctx).expr / other.m_real(ctx=ctx).expr)
        return type(self)(expr=self.expr / other.m_fp(ctx=ctx).expr)

    @methods.add(name='__mod__')
    def m_mod(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if isinstance(other, types.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (types.float, types.int)):
            return self._bad_bin_op(other, op='%', ctx=ctx)
        expr = self.expr % other.m_fp(ctx=ctx).expr
        return type(self)(expr=expr)
