# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import if_expr, unwrap
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort
    from ._float import FloatSort, RealSort
    from ._str import StrSort


INT_BITS = 64


@registry.add
class IntSort(ProxySort):
    type_name = 'int'
    methods = ProxySort.methods.copy()

    def __init__(self, expr) -> None:
        assert z3.is_int(expr), f'expected int, given {type(expr)}'
        self.expr = expr

    @classmethod
    def val(cls, x: int) -> 'IntSort':
        return cls(expr=z3.IntVal(x))

    @methods.add(name='__int__')
    @methods.add(name='conjugate')
    @methods.add(name='numerator', prop=True)
    @methods.add(name='real', prop=True)
    def m_int(self, ctx: 'Context') -> 'IntSort':
        return self

    @methods.add(name='__float__')
    def m_float(self, ctx: 'Context') -> 'RealSort':
        # TODO: int to fp?
        return self.m_real(ctx=ctx)

    def m_real(self, ctx: 'Context') -> 'RealSort':
        # app
        from ._float import RealSort
        return RealSort(z3.ToReal(self.expr)).m_real(ctx=ctx)

    def m_fp(self, ctx: 'Context'):
        # app
        from ._float import RealSort
        expr = z3.ToReal(self.expr)
        return RealSort(expr).m_fp(ctx=ctx)

    @methods.add(name='__str__')
    def m_str(self, ctx: 'Context') -> 'StrSort':
        return registry.str(expr=z3.IntToStr(self.expr))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        return registry.bool(expr=self.expr != z3.IntVal(0))

    @property
    def abs(self) -> 'IntSort':
        expr = z3.If(self.expr >= z3.IntVal(0), self.expr, -self.expr)
        return type(self)(expr=expr)

    def _math_op(self, other: ProxySort, handler: typing.Callable, ctx: 'Context') -> ProxySort:
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.m_int(ctx=ctx)
        result = super()._math_op(other=other, handler=handler, ctx=ctx)
        if as_float:
            return result.m_float(ctx=ctx)
        return result

    @methods.add(name='__add__')
    def m_add(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    @methods.add(name='__sub__')
    def m_sub(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='-', ctx=ctx)
        return self._math_op(other=other, handler=operator.__sub__, ctx=ctx)

    @methods.add(name='__mul__')
    def m_mul(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if isinstance(other, (registry.str, registry.tuple)):
            return other.m_mul(self, ctx=ctx)
        if isinstance(other, (registry.int, registry.float)):
            return self._math_op(other=other, handler=operator.__mul__, ctx=ctx)
        return self._bad_bin_op(other, op='*', ctx=ctx)

    @methods.add(name='__pow__')
    def m_pow(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='** or pow()', ctx=ctx)
        return self._math_op(other=other, handler=operator.__pow__, ctx=ctx)

    @methods.add(name='__truediv__')
    def m_truediv(self, other: ProxySort, ctx: 'Context') -> 'FloatSort':
        real = z3.ToReal(self.expr)
        if isinstance(other, (registry.int, registry.bool)):
            return registry.float(expr=real / other.m_real(ctx=ctx).expr)
        if not isinstance(other, registry.float):
            self._bad_bin_op(other, op='/', ctx=ctx)
            return self.m_float(ctx=ctx)
        if other.is_real:
            expr = real / other.m_real(ctx=ctx).expr
        else:
            expr = self.m_fp(ctx=ctx).expr / other.m_fp(ctx=ctx).expr
        return registry.float(expr=expr)

    @methods.add(name='__floordiv__')
    def m_floordiv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='//', ctx=ctx)
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.m_int(ctx=ctx)
        zero = self.val(0).expr
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr / other.expr,
            val_else=-self.expr / -other.expr,
            ctx=ctx,
        )
        if as_float:
            return result.m_float(ctx=ctx)
        return result

    @methods.add(name='__mod__')
    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if isinstance(other, registry.bool):
            other = other.m_int(ctx=ctx)
        if not isinstance(other, (registry.int, registry.float)):
            return self._bad_bin_op(other, op='%', ctx=ctx)
        as_float = isinstance(other, registry.float)
        if as_float:
            other = other.m_int(ctx=ctx)
        zero = self.val(0).expr
        result = if_expr(
            test=other.expr >= zero,
            val_then=self.expr % other.expr,
            val_else=-(-self.expr % -other.expr),
            ctx=ctx,
        )
        if as_float:
            return result.m_float(ctx=ctx)
        return result

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'IntSort':
        expr = z3.BV2Int(~z3.Int2BV(self.expr, INT_BITS))
        zero = z3.IntVal(0)
        modulo = z3.IntVal(2 ** INT_BITS)
        expr = z3.If(self.expr >= zero, expr - modulo, expr)
        return type(self)(expr=expr)

    def _bitwise_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'IntSort':
        expr = z3.BV2Int(handler(
            z3.Int2BV(self.expr, INT_BITS),
            z3.Int2BV(other.expr, INT_BITS),
        ))
        return type(self)(expr=expr)

    @methods.add(name='__and__')
    def m_and(self, other: 'ProxySort', ctx: 'Context'):
        """self & other
        """
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='&', ctx=ctx)
        return self._bitwise_op(other=other, handler=operator.__and__, ctx=ctx)

    @methods.add(name='__or__')
    def m_or(self, other: 'ProxySort', ctx: 'Context'):
        """self | other
        """
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='|', ctx=ctx)
        return self._bitwise_op(other=other, handler=operator.__or__, ctx=ctx)

    @methods.add(name='__xor__')
    def m_xor(self, other: 'ProxySort', ctx: 'Context'):
        """self ^ other
        """
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='^', ctx=ctx)
        return self._bitwise_op(other=other, handler=operator.__xor__, ctx=ctx)

    @methods.add(name='__lshift__')
    def m_lshift(self, other: 'ProxySort', ctx: 'Context'):
        """self << other
        """
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='<<', ctx=ctx)
        return self._bitwise_op(other=other, handler=operator.__lshift__, ctx=ctx)

    @methods.add(name='__rshift__')
    def m_rshift(self, other: 'ProxySort', ctx: 'Context'):
        """self >> other
        """
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='>>', ctx=ctx)
        return self._bitwise_op(other=other, handler=operator.__rshift__, ctx=ctx)

    def _comp_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'BoolSort':
        if isinstance(other, registry.float):
            return self.m_float(ctx=ctx)._comp_op(other=other, handler=handler, ctx=ctx)
        return super()._comp_op(other=other, handler=handler, ctx=ctx)

    @methods.add(name='denominator', prop=True)
    def m_denominator(self, ctx: 'Context') -> 'IntSort':
        return self.val(1)

    @methods.add(name='imag', prop=True)
    def m_imag(self, ctx: 'Context') -> 'IntSort':
        return self.val(0)

    @methods.add(name='as_integer_ratio')
    @methods.add(name='bit_length')
    @methods.add(name='from_bytes')
    @methods.add(name='to_bytes')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
