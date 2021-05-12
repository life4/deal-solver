# stdlib
import typing

# external
import z3

# app
from ._funcs import random_name
from ._proxy import ProxySort
from ._registry import registry
from .._exceptions import UnsupportedError
from .._cached_property import cached_property


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort


@registry.add
class DictSort(ProxySort):
    type_name = 'dict'
    methods = ProxySort.methods.copy()

    expr: z3.ArrayRef
    item_sort: z3.DatatypeSortRef
    value_sort: typing.Type[ProxySort]

    def __init__(self, expr, item_sort, value_sort: type) -> None:
        assert z3.is_array(expr)
        assert type(item_sort) is z3.DatatypeSortRef
        assert value_sort is not None
        self.expr = expr
        self.item_sort = item_sort
        self.value_sort = value_sort

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
            expr=z3.K(dom=key_sort, v=item),
            item_sort=item_sort,
            value_sort=type(value),
        )

    @methods.add(name='__setitem__', pure=False)
    def m_setitem(self, key: ProxySort, value: ProxySort, ctx: 'Context') -> 'DictSort':
        cls = type(self)
        item = self.item_sort.new(z3.BoolVal(True), value.expr)
        expr = z3.Update(self.expr, key.expr, item)
        return cls(
            expr=expr,
            item_sort=self.item_sort,
            value_sort=type(value),
        )

    @methods.add(name='__getitem__', pure=False)
    def m_getitem(self, key: ProxySort, ctx: 'Context') -> ProxySort:
        from .._context import ExceptionInfo

        item = z3.Select(self.expr, key.expr)
        expr = z3.Not(self.item_sort.exists(item))
        ctx.exceptions.add(ExceptionInfo(
            name='KeyError',
            names={'KeyError', 'LookupError', 'Exception', 'BaseException'},
            cond=registry.bool(expr),
        ))

        expr = self.item_sort.value(item)
        return self.value_sort(expr)

    @methods.add(name='copy')
    def m_copy(self, ctx: 'Context') -> 'DictSort':
        return self

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'DictSort':
        cls = type(self)
        item = self.expr.default()
        return cls(
            expr=z3.K(self.expr.domain(), item),
            item_sort=self.item_sort,
            value_sort=self.value_sort,
        )

    @methods.add(name='__contains__')
    def m_contains(self, key: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        item = z3.Select(self.expr, key.expr)
        expr = self.item_sort.exists(item)
        return registry.bool(expr=expr)

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


class UntypedDictSort(DictSort):
    methods = DictSort.methods.copy()

    def __init__(self) -> None:
        pass

    @cached_property
    def item_sort(self):
        item_sort = z3.Datatype('dict_val__int')
        item_sort.declare(
            'new',
            ('exists', z3.BoolSort()),
            ('value', z3.IntSort()),
        )
        return item_sort.create()

    @property
    def expr(self):
        item = self.item_sort.new(z3.BoolVal(False), z3.IntVal(0))
        return z3.K(dom=z3.IntSort(), v=item)

    @methods.add(name='__setitem__', pure=False)
    def m_setitem(self, key: ProxySort, value: ProxySort, ctx: 'Context') -> 'DictSort':
        dict_val = DictSort.make_empty(
            key_sort=key.sort(),
            value=value,
        )
        return dict_val.m_setitem(key=key, value=value, ctx=ctx)

    @methods.add(name='__getitem__', pure=False)
    def m_getitem(self, key: ProxySort, ctx: 'Context') -> ProxySort:
        ctx.add_exception(KeyError, '')
        return registry.int.val(0)

    @methods.add(name='clear', pure=False)
    def m_clear(self, ctx: 'Context') -> 'DictSort':
        return self

    @methods.add(name='__contains__')
    def m_contains(self, key: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        return registry.bool.val(False)
