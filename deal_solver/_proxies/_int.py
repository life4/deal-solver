# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import wrap, if_expr
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class IntSort(ProxySort):
    type_name = 'int'

    @classmethod
    def sort(cls):
        return z3.IntSort()

    @classmethod
    def val(cls, x):
        return z3.IntVal(x)

    @property
    def as_int(self):
        return self

    @property
    def as_float(self):
        # TODO: int to fp?
        return self.as_real

    @property
    def as_real(self):
        cls = registry['float']
        return cls(expr=z3.ToReal(self.expr))

    @property
    def as_fp(self):
        expr = z3.ToReal(self.expr)
        return wrap(expr).as_fp

    @property
    def as_str(self):
        cls = registry['str']
        return cls(expr=z3.IntToStr(self.expr))

    @property
    def as_bool(self):
        return self.expr != z3.IntVal(0)

    @property
    def abs(self):
        cls = type(self)
        expr = z3.If(self.expr >= z3.IntVal(0), self.expr, -self.expr)
        return cls(expr=expr)

    def _math_op(self, other, handler):
        float_proxy = registry['float']
        as_float = isinstance(other, float_proxy)
        if as_float:
            other = other.as_int
        result = super()._math_op(other=other, handler=handler)
        if as_float:
            return result.as_float
        return result

    def __truediv__(self, other):
        cls = registry['float']
        real = z3.ToReal(self.expr)
        if isinstance(other, IntSort):
            return cls(expr=real / other.as_real.expr)
        if not isinstance(other, cls):
            raise UnsupportedError('unsupported denominator sort', other.sort())
        if other.is_real:
            expr = real / other.as_real.expr
        else:
            expr = self.as_fp.expr / other.as_fp.expr
        return cls(expr=expr)

    def __floordiv__(self, other):
        float_proxy = registry['float']
        as_float = isinstance(other, float_proxy)
        if as_float:
            other = other.as_int
        zero = self.val(0)
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr / other.expr,
            val_else=-self.expr / -other.expr,
        )
        if as_float:
            return result.as_float
        return result

    def __mod__(self, other):
        float_proxy = registry['float']
        as_float = isinstance(other, float_proxy)
        if as_float:
            other = other.as_int
        zero = self.val(0)
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr % other.expr,
            val_else=-(-self.expr % -other.expr),
        )
        if as_float:
            return result.as_float
        return result
