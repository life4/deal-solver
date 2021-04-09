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
    methods = ProxySort.methods.copy()

    def __init__(self, expr) -> None:
        assert z3.is_bool(expr) or z3.is_seq(expr), f'expected bool, given {type(expr)}'
        self.expr = expr

    @classmethod
    def val(cls, x) -> 'BoolSort':
        return cls(expr=z3.BoolVal(x))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        return self

    @methods.add(name='__int__')
    def m_int(self, ctx: 'Context') -> 'IntSort':
        return if_expr(self, registry.int.val(1), registry.int.val(0), ctx=ctx)

    @methods.add(name='__float__')
    def m_float(self, ctx: 'Context') -> 'FloatSort':
        return self.m_int(ctx=ctx).m_float(ctx=ctx)

    def m_real(self, ctx: 'Context') -> 'RealSort':
        return self.m_int(ctx=ctx).m_real(ctx=ctx)

    def m_fp(self, ctx: 'Context') -> 'FPSort':
        return self.m_int(ctx=ctx).m_fp(ctx=ctx)

    @methods.add(name='__add__')
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        return self.m_int(ctx=ctx).m_add(other, ctx=ctx)

    @methods.add(name='__mod__')
    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='%', ctx=ctx)
        return self.m_int(ctx=ctx).m_mod(other, ctx=ctx)

    @methods.add(name='__sub__')
    def m_sub(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='-', ctx=ctx)
        return self.m_int(ctx=ctx).m_sub(other, ctx=ctx)

    @methods.add(name='__mul__')
    def m_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='*', ctx=ctx)
        return self.m_int(ctx=ctx).m_mul(other, ctx=ctx)

    @methods.add(name='__truediv__')
    def m_truediv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='/', ctx=ctx)
        return self.m_int(ctx=ctx).m_truediv(other, ctx=ctx)

    @methods.add(name='__floordiv__')
    def m_floordiv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, (registry.bool, registry.float, registry.int)):
            return self._bad_bin_op(other, op='//', ctx=ctx)
        return self.m_int(ctx=ctx).m_floordiv(other, ctx=ctx)

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'ProxySort':
        return self.m_int(ctx=ctx).m_neg(ctx=ctx)

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'ProxySort':
        return self.m_int(ctx=ctx).m_pos(ctx=ctx)

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'ProxySort':
        return self.m_int(ctx=ctx).m_inv(ctx=ctx)
