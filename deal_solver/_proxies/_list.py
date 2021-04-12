# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap
from ._var_tuple import VarTupleSort
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context


@registry.add
class ListSort(VarTupleSort):
    expr: z3.SeqRef
    type_name = 'list'
    methods = VarTupleSort.methods.copy()

    @methods.add(name='copy')
    def m_copy(self, ctx: 'Context') -> 'ListSort':
        return self

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'ListSort':
        return self.make_empty(
            sort=self.expr.sort().basis(),
        )

    @methods.add(name='append', pure=False)
    def r_append(self, item: ProxySort, ctx: 'Context') -> 'ListSort':
        cls = type(self)
        unit = z3.Unit(unwrap(item))
        self._ensure(item)
        return cls(expr=self.expr + unit)

    @methods.add(name='extend', pure=False)
    def r_extend(self, other: ProxySort, ctx: 'Context') -> 'ProxySort':
        return self.m_add(other, ctx=ctx)

    @methods.add(name='__add__')
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.list):
            msg = 'can only concatenate {s} (not "{o}") to {s}'
            msg = msg.format(s=self.type_name, o=other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    @methods.add(name='insert')
    @methods.add(name='pop')
    @methods.add(name='remove')
    @methods.add(name='reverse', pure=False)
    @methods.add(name='sort', pure=False)
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
