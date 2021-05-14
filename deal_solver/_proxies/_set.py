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
        assert z3.is_array(expr)
        self.expr = expr

    @staticmethod
    def make_empty_expr(sort):
        return z3.EmptySet(sort)

    @classmethod
    def make_empty(cls, sort: z3.SortRef) -> 'SetSort':
        expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @classmethod
    def from_items(cls, values: typing.List[ProxySort], ctx: 'Context') -> 'SetSort':
        assert values
        items = cls.make_empty_expr(sort=unwrap(values[0]).sort())
        for value in values:
            items = z3.SetAdd(items, value.expr)
        return cls(expr=items)

    @methods.add(name='add', pure=False)
    def r_add(self, item: 'ProxySort', ctx: 'Context') -> 'SetSort':
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
        empty = self.make_empty(sort=other.expr.domain())
        return self.m_and(other, ctx=ctx).m_eq(empty, ctx=ctx)

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

    @methods.add(name='__eq__')
    def m_eq(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        # type mismatch
        if not isinstance(other, registry.set):
            return registry.bool.val(False)
        # other is untyped
        if isinstance(other, UntypedSetSort):
            empty = self.make_empty_expr(sort=self.expr.domain())
            expr = self.expr == empty
            return registry.bool(expr=expr)
        return super().m_eq(other, ctx=ctx)

    @methods.add(name='pop')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)


class UntypedSetSort(SetSort):
    methods = SetSort.methods.copy()

    def __init__(self) -> None:
        pass

    @staticmethod
    def sort() -> z3.SeqSortRef:
        return z3.SeqSort(z3.IntSort())

    @property
    def expr(self):
        return z3.Empty(self.sort())

    @methods.add(name='add', pure=False)
    def r_add(self, item: 'ProxySort', ctx: 'Context') -> 'SetSort':
        result = SetSort.make_empty(item.sort())
        return result.r_add(item, ctx=ctx)

    @methods.add(name='__eq__')
    def m_eq(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        # type mismatch
        if not isinstance(other, registry.set):
            return registry.bool.val(False)
        # both are empty
        if isinstance(other, type(self)):
            return registry.bool.val(True)
        # other is a typed set
        empty = SetSort.make_empty(sort=other.expr.domain())
        return other.m_eq(empty, ctx=ctx)
