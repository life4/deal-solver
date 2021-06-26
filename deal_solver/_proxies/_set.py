import typing

import z3

from ._funcs import random_name
from ._method import Mutation
from ._proxy import ProxySort
from ._registry import types
from ._type_factory import TypeFactory


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort
    from ._list import ListSort


@types.add
class SetSort(ProxySort):
    type_name = 'set'
    methods = ProxySort.methods.copy()
    expr: z3.ArrayRef
    subtypes: typing.Tuple[TypeFactory, ...]

    def __init__(self, expr, subtypes=()) -> None:
        assert len(subtypes) == 1
        assert z3.is_array(expr)
        self.expr = expr
        self.subtypes = subtypes

    def evolve(self, **kwargs):
        params = dict(expr=self.expr, subtypes=self.subtypes)
        params.update(kwargs)
        return type(self)(**params)

    @classmethod
    def var(cls, subtype: ProxySort = None, *, name: str, ctx: z3.Context) -> 'SetSort':
        from .._context import Context
        assert subtype
        expr = z3.Const(name=name, sort=z3.SetSort(subtype.sort()))
        ctx = Context.make_empty(get_contracts=None, z3_ctx=ctx)
        return cls(expr=expr, subtypes=(subtype.factory, ))

    @property
    def factory(self) -> TypeFactory:
        sort = self.expr.domain()
        expr = self.make_empty_expr(sort)
        empty = self.evolve(expr=expr)
        return TypeFactory(
            type=type(self),
            default=empty,
            subtypes=self.subtypes,
        )

    @staticmethod
    def make_empty_expr(sort):
        return z3.EmptySet(sort)

    @classmethod
    def val(cls, values: typing.List[ProxySort], ctx: 'Context') -> 'SetSort':
        assert values  # there is no literal for empty set
        items = cls.make_empty_expr(sort=values[0].expr.sort())
        for value in values:
            items = z3.SetAdd(items, value.expr)
        value_type = values[0].factory
        return cls(expr=items, subtypes=(value_type,))

    @methods.add(name='add', pure=False)
    def r_add(self, item: ProxySort, ctx: 'Context') -> 'SetSort':
        return self.evolve(
            expr=z3.SetAdd(s=self.expr, e=item.expr),
        )

    @methods.add(name='copy')
    def r_copy(self, ctx: 'Context') -> 'SetSort':
        return self

    @methods.add(name='clear', pure=False)
    def r_clear(self, ctx: 'Context') -> 'SetSort':
        sort = self.expr.sort().domain()
        expr = self.make_empty_expr(sort)
        return self.evolve(expr=expr)

    @methods.add(name='__contains__')
    def m_contains(self, item: ProxySort, ctx: 'Context') -> 'BoolSort':
        return types.bool(expr=z3.IsMember(e=item.expr, s=self.expr))

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
    def m_or(self, other: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: `set.union` supports any iterable
        if not isinstance(other, types.set):
            return self._bad_bin_op(other=other, op='|', ctx=ctx)
        expr = z3.SetUnion(self.expr, other.expr)
        return self.evolve(expr=expr)

    @methods.add(name='intersection')
    @methods.add(name='intersection_update', pure=False)
    @methods.add(name='__and__')
    def m_and(self, other: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: `set.intersection` supports any iterable
        if not isinstance(other, types.set):
            return self._bad_bin_op(other=other, op='&', ctx=ctx)
        expr = z3.SetIntersect(self.expr, other.expr)
        return self.evolve(expr=expr)

    @methods.add(name='symmetric_difference')
    @methods.add(name='symmetric_difference_update', pure=False)
    @methods.add(name='__xor__')
    def m_xor(self, other: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: `set.symmetric_difference` supports any iterable
        if not isinstance(other, types.set):
            return self._bad_bin_op(other=other, op='^', ctx=ctx)
        expr = z3.SetUnion(
            z3.SetDifference(self.expr, other.expr),
            z3.SetDifference(other.expr, self.expr),
        )
        return self.evolve(expr=expr)

    @methods.add(name='difference')
    @methods.add(name='difference_update', pure=False)
    def r_difference(self, other: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: `set.difference` supports any iterable
        if not isinstance(other, types.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        expr = z3.SetDifference(self.expr, other.expr)
        return self.evolve(expr=expr)

    @methods.add(name='issuperset')
    def r_issuperset(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # TODO: `set.issuperset` supports any iterable
        if not isinstance(other, types.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return types.bool.val(False, ctx=ctx)
        return other.r_issubset(self, ctx=ctx)

    @methods.add(name='issubset')
    def r_issubset(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # TODO: `set.issubset` supports any iterable
        if not isinstance(other, types.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return types.bool.val(False, ctx=ctx)
        expr = z3.IsSubset(self.expr, other.expr)
        return types.bool(expr=expr)

    @methods.add(name='isdisjoint')
    def r_isdisjoint(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # TODO: `set.isdisjoint` supports any iterable
        if not isinstance(other, types.set):
            msg = "'{}' object is not iterable".format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return types.bool.val(False, ctx=ctx)
        sort = other.expr.domain()
        expr = self.make_empty_expr(sort)
        empty = self.evolve(expr=expr)
        return self.m_and(other, ctx=ctx).m_eq(empty, ctx=ctx)

    @methods.add(name='discard', pure=False)
    def r_discard(self, item: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: check sort
        expr = z3.SetDel(self.expr, item.expr)
        return self.evolve(expr=expr)

    @methods.add(name='remove', pure=False)
    def r_remove(self, item: ProxySort, ctx: 'Context') -> 'SetSort':
        # TODO: check sort
        ctx.add_exception(
            exc=KeyError,
            cond=self.m_contains(item, ctx=ctx).m_not(ctx=ctx),
        )
        expr = z3.SetDel(self.expr, item.expr)
        return self.evolve(expr=expr)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # type mismatch
        if not isinstance(other, types.set):
            return types.bool.val(False, ctx=ctx)
        # other is untyped
        if isinstance(other, UntypedSetSort):
            empty = self.make_empty_expr(sort=self.expr.domain())
            expr = self.expr == empty
            return types.bool(expr=expr)
        return super().m_eq(other, ctx=ctx)

    def m_list(self, ctx: 'Context') -> 'ListSort':
        sort = self.expr.domain()
        expr = z3.Const(random_name('set2list'), z3.SeqSort(sort))
        x = z3.Const(random_name('set_item'), sort)
        ctx.given.add(types.bool(
            z3.ForAll([x], z3.And(
                z3.Implies(
                    z3.IsMember(e=x, s=self.expr),
                    z3.Contains(expr, z3.Unit(x)),
                ),
                # TODO: correct but slow as hell
                # z3.IndexOf(expr, z3.Unit(x), 0) == z3.LastIndexOf(expr, z3.Unit(x)),
            )),
        ))
        return types.list(expr=expr, subtypes=self.subtypes)

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        return self.m_list(ctx=ctx).m_len(ctx=ctx)

    @methods.add(name='pop', pure=False)
    def r_pop(self, ctx: 'Context') -> Mutation:
        # TODO: KeyError for empty set
        expr = z3.Const(random_name('set_item'), self.expr.domain())
        item = self.subtypes[0].wrap(expr)
        ctx.given.add(self.m_contains(item, ctx=ctx))
        return Mutation(
            new_value=self.evolve(expr=z3.SetDel(self.expr, item.expr)),
            result=item,
        )


class UntypedSetSort(SetSort):
    methods = SetSort.methods.copy()

    def __init__(self, expr=None, subtypes=None) -> None:
        pass

    @property
    def factory(self) -> TypeFactory:
        return TypeFactory(
            type=type(self),
            default=self,
            subtypes=(),
        )

    def evolve(self, **kwargs):
        raise NotImplementedError

    @staticmethod
    def sort() -> z3.SeqSortRef:
        return z3.SetSort(z3.IntSort())

    @property
    def expr(self):
        return z3.EmptySet(self.sort())

    @methods.add(name='add', pure=False)
    def r_add(self, item: ProxySort, ctx: 'Context') -> 'SetSort':
        expr = self.make_empty_expr(item.sort())
        subtype = item.factory
        result = SetSort(expr, subtypes=(subtype,))
        return result.r_add(item, ctx=ctx)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # type mismatch
        if not isinstance(other, types.set):
            return types.bool.val(False, ctx=ctx)
        # both are empty
        if isinstance(other, type(self)):
            return types.bool.val(True, ctx=ctx)
        # other is a typed set
        sort = other.expr.domain()
        expr = other.make_empty_expr(sort)
        empty = other.evolve(expr=expr)
        return other.m_eq(empty, ctx=ctx)

    @methods.add(name='pop', pure=False)
    def r_pop(self, ctx: 'Context') -> Mutation:
        ctx.add_exception(KeyError, 'pop from an empty set')
        return Mutation(new_value=self, result=self)

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        return types.int.val(0, ctx=ctx)
