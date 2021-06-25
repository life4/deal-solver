import typing

import z3

from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import types
from ._var_tuple import VarTupleSort
from ._type_factory import TypeFactory


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort


@types.add
class ListSort(VarTupleSort):
    expr: z3.SeqRef
    type_name = 'list'
    methods = VarTupleSort.methods.copy()

    @methods.add(name='copy')
    def m_copy(self, ctx: 'Context') -> 'ListSort':
        return self

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'ListSort':
        sort = self.expr.sort().basis()
        expr = self.make_empty_expr(sort)
        return self.evolve(expr=expr)

    @methods.add(name='append', pure=False)
    def r_append(self, item: ProxySort, ctx: 'Context') -> 'ListSort':
        if not self.subtypes[0].match(item.factory):
            msg = 'element has type {}, expected {}'
            msg = msg.format(item.type_name, self.subtypes[0].type_name)
            raise UnsupportedError(msg)
        unit = z3.Unit(item.expr)
        return self.evolve(expr=self.expr + unit)

    @methods.add(name='extend', pure=False)
    def r_extend(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        return self.m_add(other, ctx=ctx)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        if isinstance(other, UntypedListSort):
            empty = self.make_empty_expr(sort=self.sort().basis())
            expr = self.expr == empty
            return types.bool(expr=expr)
        if not self.factory.match(other.factory):
            return types.bool.val(False, ctx=ctx)
        return super().m_eq(other, ctx=ctx)

    @methods.add(name='insert')
    @methods.add(name='pop')
    @methods.add(name='remove')
    @methods.add(name='reverse', pure=False)
    @methods.add(name='sort', pure=False)
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)


class UntypedListSort(ListSort):
    methods = ListSort.methods.copy()

    def __init__(self, expr=None, subtypes=None) -> None:
        pass

    @property
    def subtypes(self):
        raise NotImplementedError

    @property
    def factory(self) -> TypeFactory:
        return TypeFactory(
            type=type(self),
            default=self,
            subtypes=(),
        )

    @staticmethod
    def sort() -> z3.SeqSortRef:
        return z3.SeqSort(z3.IntSort())

    @property
    def expr(self):
        return z3.Empty(self.sort())

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        return types.bool.val(False, ctx=ctx)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: ProxySort, ctx: 'Context') -> ProxySort:
        if not isinstance(index, types.int):
            msg = '{} indices must be integers or slices, not {}'
            msg = msg.format(self.type_name, index.type_name)
            ctx.add_exception(exc=TypeError, msg=msg)
            return types.int.val(0, ctx=ctx)
        msg = '{} index out of range'.format(self.type_name)
        ctx.add_exception(IndexError, msg)
        return self

    def get_slice(self, start: ProxySort, stop: ProxySort, ctx: 'Context') -> ProxySort:
        return self

    @methods.add(name='__contains__')
    def m_contains(self, item: ProxySort, ctx: 'Context') -> 'BoolSort':
        return types.bool.val(False, ctx=ctx)

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        return types.int(expr=z3.IntVal(0))

    @methods.add(name='count')
    def r_count(self, item: ProxySort, ctx: 'Context') -> 'IntSort':
        return types.int(expr=z3.IntVal(0))

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'ListSort':
        return self

    @methods.add(name='append', pure=False)
    def r_append(self, item: ProxySort, ctx: 'Context') -> 'ListSort':
        return ListSort.val([item], ctx=ctx)

    @methods.add(name='__add__', pure=False)
    def m_add(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if not isinstance(other, types.list):
            msg = 'can only concatenate {s} (not "{o}") to {s}'
            msg = msg.format(s=self.type_name, o=other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return other

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        if isinstance(other, UntypedListSort):
            return types.bool.val(True, ctx=ctx)
        if isinstance(other, types.list):
            return other.m_eq(other.factory.default, ctx=ctx)
        return types.bool.val(False, ctx=ctx)
