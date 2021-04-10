# stdlib
import typing

# external
import z3

# app
from ._funcs import unwrap
from ._proxy import ProxySort
from ._registry import registry
from .._exceptions import UnsupportedError


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
        # assert z3.is_array(expr)
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

    @methods.add(name='difference')
    @methods.add(name='difference_update', pure=False)
    @methods.add(name='discard', pure=False)
    @methods.add(name='intersection')
    @methods.add(name='intersection_update', pure=False)
    @methods.add(name='isdisjoint')
    @methods.add(name='issubset')
    @methods.add(name='issuperset')
    @methods.add(name='pop')
    @methods.add(name='remove')
    @methods.add(name='symmetric_difference')
    @methods.add(name='symmetric_difference_update', pure=False)
    @methods.add(name='union')
    @methods.add(name='update', pure=False)
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
