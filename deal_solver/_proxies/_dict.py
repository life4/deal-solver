# stdlib
import typing

# external
import z3

# app
from ._funcs import random_name
from ._proxy import ProxySort
from ._registry import registry
from .._exceptions import UnsupportedError


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort


@registry.add
class DictSort(ProxySort):
    type_name = 'dict'
    methods = ProxySort.methods.copy()

    expr: typing.Optional[z3.ArrayRef]
    item_sort: z3.DatatypeSortRef

    def __init__(self, expr=None, item_sort=None) -> None:
        if expr is not None:
            assert z3.is_array(expr)
            assert type(item_sort) is z3.DatatypeSortRef
        self.expr = expr
        self.item_sort = item_sort

    @classmethod
    def make_empty(cls, key_sort: z3.SortRef, value: ProxySort) -> 'DictSort':
        item_sort = z3.Datatype(random_name('dict_val'))
        item_sort.declare(
            'new',
            ('exists', z3.BoolSort()),
            ('value', value.sort()),
        )
        item_sort = item_sort.create()
        item = item_sort.new(z3.BoolVal(False), value.expr)
        return cls(
            expr=z3.K(key_sort, item),
            item_sort=item_sort,
        )

    @methods.add(name='__setitem__', pure=False)
    def m_setitem(self, key: ProxySort, value: ProxySort, ctx: 'Context') -> 'DictSort':
        cls = type(self)
        if self.expr is None:
            self = cls.make_empty(
                key_sort=key.sort(),
                value=value,
            )
        item = self.item_sort.new(z3.BoolVal(True), value.expr)
        expr = z3.Update(self.expr, key.expr, item)
        return cls(expr=expr, item_sort=self.item_sort)

    @methods.add(name='copy')
    def m_copy(self, ctx: 'Context') -> 'DictSort':
        return self

    @methods.add(name='__contains__')
    def m_contains(self, key: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        if self.expr is None:
            return registry.bool.val(False)
        item = z3.Select(self.expr, key.expr)
        expr = self.item_sort.exists(item)
        return registry.bool(expr=expr)

    @methods.add(name='clear')
    @methods.add(name='fromkeys')
    @methods.add(name='get')
    @methods.add(name='items')
    @methods.add(name='keys')
    @methods.add(name='pop')
    @methods.add(name='popitem')
    @methods.add(name='setdefault')
    @methods.add(name='update')
    @methods.add(name='values')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
