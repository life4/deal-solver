# stdlib
from sys import float_info
import typing

# external
import z3

# app
from ._funcs import switch, wrap, and_expr
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import registry

if typing.TYPE_CHECKING:
    from ._bool import BoolSort
    from ._int import IntSort


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

    def __init__(self, expr) -> None:
        self.expr = expr

    @classmethod
    def sort(cls, ctx: z3.Context = None):
        if cls.prefer_real:
            return RealSort.sort(ctx=ctx)
        return FPSort.sort(ctx=ctx)

    @classmethod
    def val(cls, x: float, ctx: z3.Context = None) -> 'FloatSort':
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

    def __floordiv__(self, other: ProxySort) -> 'FloatSort':
        if self.is_real and other.is_real:
            return (self / other).as_int.as_float

        zero = self.val(0.0)
        one = self.val(1.0)
        nan = z3.fpNaN(self.sort())
        return switch(  # type: ignore
            (z3.fpIsInf(self.expr), nan),
            (z3.Not(z3.fpIsInf(other.expr)), (self / other).as_int.as_fp),
            (z3.fpIsZero(self.expr), zero),
            (and_expr(self < zero, other < zero), zero),
            (and_expr(self > zero, other > zero), zero),
            default=-one,
        )

    __mul__: typing.Callable[['FloatSort', ProxySort], 'FloatSort']


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

    def _binary_op(self, other: ProxySort, handler: typing.Callable) -> ProxySort:
        if isinstance(other, registry.int):
            return wrap(handler(self.expr, other.as_real.expr))
        if not isinstance(other, FloatSort):
            raise UnsupportedError('cannot combine float and', type(other))
        if other.is_real:
            return wrap(handler(self.expr, other.expr))
        if self.prefer_real:
            return wrap(handler(self.expr, other.as_real.expr))
        return wrap(handler(self.as_fp.expr, other.expr))

    def __truediv__(self, other: ProxySort) -> FloatSort:
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

    def _binary_op(self, other: ProxySort, handler: typing.Callable) -> ProxySort:
        if isinstance(other, registry.int):
            return wrap(handler(self.expr, other.as_fp.expr))
        if not isinstance(other, FloatSort):
            raise UnsupportedError('cannot combine float and', type(other))
        if other.is_fp:
            return wrap(handler(self.expr, other.expr))
        if self.prefer_real:
            return wrap(handler(self.as_real.expr, other.expr))
        return wrap(handler(self.expr, other.as_fp.expr))

    def __truediv__(self, other: ProxySort) -> 'FloatSort':
        if isinstance(other, registry.int):
            return type(self)(expr=self.as_fp.expr / other.as_fp.expr)

        if other.is_fp:
            return type(self)(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.as_real.expr / other.as_real.expr)
        return type(self)(expr=self.expr / other.as_fp.expr)

    def __eq__(self, other) -> 'BoolSort':  # type: ignore
        return self._comp_op(other=other, handler=z3.fpEQ)

    def __ne__(self, other) -> 'BoolSort':  # type: ignore
        return self._comp_op(other=other, handler=z3.fpNEQ)

    def __gt__(self, other) -> 'BoolSort':
        return self._comp_op(other=other, handler=z3.fpGT)

    def __ge__(self, other) -> 'BoolSort':
        return self._comp_op(other=other, handler=z3.fpGEQ)

    def __lt__(self, other) -> 'BoolSort':
        return self._comp_op(other=other, handler=z3.fpLT)

    def __le__(self, other) -> 'BoolSort':
        return self._comp_op(other=other, handler=z3.fpLEQ)
