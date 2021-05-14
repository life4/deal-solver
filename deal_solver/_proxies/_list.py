# stdlib
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap
from ._proxy import ProxySort
from ._registry import registry
from ._var_tuple import VarTupleSort


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._int import IntSort
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

    def __init__(self) -> None:
        pass

    @staticmethod
    def sort() -> z3.SeqSortRef:
        return z3.SeqSort(z3.IntSort())

    @property
    def expr(self):
        return z3.Empty(self.sort())

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        return registry.bool.val(False)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        msg = '{} index out of range'.format(self.type_name)
        ctx.add_exception(IndexError, msg)
        return self

    def get_slice(self, start: 'ProxySort', stop: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        return self

    @methods.add(name='__contains__')
    def m_contains(self, item: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        return registry.bool.val(False)

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        return registry.int(expr=z3.IntVal(0))

    @methods.add(name='count')
    def r_count(self, item: 'ProxySort', ctx: 'Context') -> 'IntSort':
        return registry.int(expr=z3.IntVal(0))

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'ListSort':
        return self

    @methods.add(name='append', pure=False)
    def r_append(self, item: ProxySort, ctx: 'Context') -> 'ListSort':
        return ListSort.from_items([item], ctx=ctx)

    @methods.add(name='__add__', pure=False)
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, ListSort):
            msg = 'can only concatenate {s} (not "{o}") to {s}'
            msg = msg.format(s=self.type_name, o=other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return other
