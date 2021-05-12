# stdlib
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import not_expr, unwrap
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort


@registry.add
class SetSort(ProxySort):
    type_name = 'set'
    methods = ProxySort.methods.copy()
    expr: z3.ArrayRef

    def __init__(self, expr) -> None:
        if expr is not None:
            assert z3.is_array(expr)
        self.expr = expr

    @staticmethod
    def make_empty_expr(sort):
        return z3.EmptySet(sort)

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SetSort':
        expr = None
        if sort is not None:
            expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @methods.add(name='add', pure=False)
    def r_add(self, item: 'ProxySort', ctx: 'Context') -> 'SetSort':
        self._ensure(item)
        return registry.set(
            expr=z3.SetAdd(s=self.expr, e=unwrap(item)),
        )

    @methods.add(name='copy')
    def r_copy(self, ctx: 'Context') -> 'SetSort':
        return self

    @methods.add(name='clear', pure=False)
    def r_clear(self, ctx: 'Context') -> 'SetSort':
        sort = self.expr.sort().domain()
        return self.make_empty(sort=sort)

    @methods.add(name='__contains__')
    def m_contains(self, item: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        self._ensure(item)
        return registry.bool(expr=z3.IsMember(e=unwrap(item), s=self.expr))

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'SetSort':
        return self._bad_un_op(op='+', ctx=ctx)

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'SetSort':
        return self._bad_un_op(op='-', ctx=ctx)

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'SetSort':
        return self._bad_un_op(op='~', ctx=ctx)

    @methods.add(name='union')
    @methods.add(name='update', pure=False)
    @methods.add(name='__or__')
    def m_or(self, other: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # TODO: `set.union` supports any iterable
        if not isinstance(other, registry.set):
            return self._bad_bin_op(other=other, op='|', ctx=ctx)
        expr = z3.SetUnion(self.expr, other.expr)
        return registry.set(expr=expr)

    @methods.add(name='intersection')
    @methods.add(name='intersection_update', pure=False)
    @methods.add(name='__and__')
    def m_and(self, other: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # TODO: `set.intersection` supports any iterable
        if not isinstance(other, registry.set):
            return self._bad_bin_op(other=other, op='&', ctx=ctx)
        expr = z3.SetIntersect(self.expr, other.expr)
        return registry.set(expr=expr)

    @methods.add(name='symmetric_difference')
    @methods.add(name='symmetric_difference_update', pure=False)
    @methods.add(name='__xor__')
    def m_xor(self, other: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # TODO: `set.symmetric_difference` supports any iterable
        if not isinstance(other, registry.set):
            return self._bad_bin_op(other=other, op='^', ctx=ctx)
        expr = z3.SetUnion(
            z3.SetDifference(self.expr, other.expr),
            z3.SetDifference(other.expr, self.expr),
        )
        return registry.set(expr=expr)

    @methods.add(name='difference')
    @methods.add(name='difference_update', pure=False)
    def r_difference(self, other: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # TODO: `set.difference` supports any iterable
        if not isinstance(other, registry.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        expr = z3.SetDifference(self.expr, other.expr)
        return registry.set(expr=expr)

    @methods.add(name='issuperset')
    def r_issuperset(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        # TODO: `set.issuperset` supports any iterable
        if not isinstance(other, registry.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return registry.bool.val(False)
        return other.r_issubset(self, ctx=ctx)

    @methods.add(name='issubset')
    def r_issubset(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        # TODO: `set.issubset` supports any iterable
        if not isinstance(other, registry.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return registry.bool.val(False)
        expr = z3.IsSubset(self.expr, other.expr)
        return registry.bool(expr=expr)

    @methods.add(name='isdisjoint')
    def r_isdisjoint(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        # TODO: `set.isdisjoint` supports any iterable
        if not isinstance(other, registry.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return registry.bool.val(False)
        return self.m_and(other, ctx=ctx).m_eq(self.make_empty(), ctx=ctx)

    @methods.add(name='discard', pure=False)
    def r_discard(self, item: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # TODO: check sort
        expr = z3.SetDel(self.expr, item.expr)
        return registry.set(expr=expr)

    @methods.add(name='remove', pure=False)
    def r_remove(self, item: 'ProxySort', ctx: 'Context') -> 'SetSort':
        # app
        from .._context import ExceptionInfo

        # TODO: check sort
        ctx.exceptions.add(ExceptionInfo(
            name='KeyError',
            names={'KeyError', 'LookupError', 'Exception', 'BaseException'},
            cond=not_expr(self.m_contains(item, ctx=ctx), ctx=ctx),
        ))
        expr = z3.SetDel(self.expr, item.expr)
        return registry.set(expr=expr)

    @methods.add(name='pop')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
