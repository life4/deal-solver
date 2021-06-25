import typing

import z3

from .._cached_property import cached_property
from .._exceptions import UnsupportedError
from ._method import Mutation
from ._proxy import ProxySort
from ._registry import types
from ._type_factory import TypeFactory


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort


@types.add
class DictSort(ProxySort):
    type_name = 'dict'
    methods = ProxySort.methods.copy()

    expr: z3.ArrayRef
    subtypes: typing.Tuple[TypeFactory, ...]

    def __init__(self, expr, subtypes: tuple) -> None:
        assert z3.is_array(expr)
        assert len(subtypes) == 2
        self.expr = expr
        self.subtypes = subtypes

    def evolve(self, **kwargs):
        params = dict(expr=self.expr, subtypes=self.subtypes)
        params.update(kwargs)
        return type(self)(**params)

    @property
    def _val_type(self) -> TypeFactory:
        return self.subtypes[1]

    @cached_property
    def item_sort(self):
        item_sort = z3.Datatype(f'dict_val__{self._val_type.type_name}')
        item_sort.declare(
            'new',
            ('exists', z3.BoolSort()),
            ('value', self._val_type.sort),
        )
        return item_sort.create()

    @classmethod
    def var(
        cls, ktype: ProxySort = None, vtype: ProxySort = None,
        *, name: str, ctx: z3.Context,
    ) -> 'DictSort':
        from .._context import Context
        assert ktype
        assert vtype
        ctx = Context.make_empty(get_contracts=None, z3_ctx=ctx)
        empty = cls.make_empty(ktype, vtype)
        expr = z3.Array(name, ktype.sort(), empty.item_sort)
        empty.expr = expr
        return empty

    @property
    def factory(self) -> TypeFactory:
        expr = z3.K(dom=self.expr.domain(), v=self.expr.default())
        empty = self.evolve(expr=expr)
        return TypeFactory(
            type=type(self),
            default=empty,
            subtypes=self.subtypes,
        )

    @classmethod
    def make_empty(cls, key: ProxySort, value: ProxySort) -> 'DictSort':
        item_sort = z3.Datatype(f'dict_val__{value.type_name}')
        item_sort.declare(
            'new',
            ('exists', z3.BoolSort()),
            ('value', value.sort()),
        )
        item_sort = item_sort.create()
        item = item_sort.new(z3.BoolVal(False), value.factory.default.expr)
        return cls(
            expr=z3.K(dom=key.sort(), v=item),
            subtypes=(
                key.factory,
                value.factory,
            ),
        )

    @methods.add(name='__setitem__', pure=False)
    def m_setitem(self, key: ProxySort, value: ProxySort, ctx: 'Context') -> 'DictSort':
        if not self.subtypes[0].match(key.factory):
            raise UnsupportedError('key has type {}, expected {}'.format(
                key.type_name,
                self.subtypes[0].type_name,
            ))
        if not self.subtypes[1].match(value.factory):
            raise UnsupportedError('value has type {}, expected {}'.format(
                value.type_name,
                self.subtypes[1].type_name,
            ))
        item = self.item_sort.new(z3.BoolVal(True), value.expr)
        expr = z3.Update(self.expr, key.expr, item)
        return self.evolve(expr=expr)

    @methods.add(name='__getitem__', pure=False)
    def m_getitem(self, key: ProxySort, ctx: 'Context') -> ProxySort:
        if not self.subtypes[0].match(key.factory):
            ctx.add_exception(exc=KeyError)
            return self.subtypes[1].default
        ctx.add_exception(
            exc=KeyError,
            cond=self.m_contains(key, ctx=ctx).m_not(ctx=ctx),
        )
        item = z3.Select(self.expr, key.expr)
        expr = self.item_sort.value(item)
        return self._val_type.wrap(expr)

    @methods.add(name='get')
    def r_get(self, key: ProxySort, default: ProxySort, *, ctx: 'Context') -> ProxySort:
        item = z3.Select(self.expr, key.expr)
        expr = z3.If(
            self.item_sort.exists(item),
            self.item_sort.value(item),
            default.expr,
        )
        return self._val_type.wrap(expr)

    @methods.add(name='copy')
    def r_copy(self, ctx: 'Context') -> 'DictSort':
        return self

    @methods.add(name='clear', pure=False)
    def r_clear(self, ctx: 'Context') -> 'DictSort':
        item = self.expr.default()
        expr = z3.K(self.expr.domain(), item)
        return self.evolve(expr=expr)

    @methods.add(name='pop', pure=False)
    def r_pop(self, key: ProxySort, ctx: 'Context') -> Mutation:
        if not self.subtypes[0].match(key.factory):
            ctx.add_exception(exc=KeyError)
            return Mutation(new_value=self, result=self.subtypes[1].default)
        ctx.add_exception(
            exc=KeyError,
            cond=self.m_contains(key, ctx=ctx).m_not(ctx=ctx),
        )
        # get the value
        item = z3.Select(self.expr, key.expr)
        expr = self.item_sort.value(item)
        result = self._val_type.wrap(expr)

        # remove the item
        expr = z3.Update(self.expr, key.expr, self.expr.default())
        new_value = self.evolve(expr=expr)
        return Mutation(new_value=new_value, result=result)

    @methods.add(name='__contains__')
    def m_contains(self, key: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not self.subtypes[0].match(key.factory):
            return types.bool.val(False, ctx=ctx)
        item = z3.Select(self.expr, key.expr)
        expr = self.item_sort.exists(item)
        return types.bool(expr=expr)

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        empty = z3.K(dom=self.expr.domain(), v=self.expr.default())
        expr = self.expr != empty
        return types.bool(expr=expr)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        if isinstance(other, UntypedDictSort):
            return other.m_eq(self, ctx=ctx)
        if not self.factory.match(other.factory):
            return types.bool.val(False, ctx=ctx)
        return super().m_eq(other, ctx=ctx)

    @methods.add(name='fromkeys')
    @methods.add(name='items')
    @methods.add(name='keys')
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

    @property
    def factory(self) -> TypeFactory:
        empty = DictSort.make_empty(
            key=types.int(expr=z3.IntVal(0)),
            value=types.int(expr=z3.IntVal(0)),
        )
        return empty.factory

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
        dict_val = DictSort.make_empty(key, value)
        return dict_val.m_setitem(key=key, value=value, ctx=ctx)

    @methods.add(name='__getitem__', pure=False)
    def m_getitem(self, key: ProxySort, ctx: 'Context') -> ProxySort:
        ctx.add_exception(KeyError, '')
        return self

    @methods.add(name='clear', pure=False)
    def r_clear(self, ctx: 'Context') -> 'DictSort':
        return self

    @methods.add(name='get')
    def r_get(self, key: ProxySort, default: ProxySort, *, ctx: 'Context') -> ProxySort:
        return default

    @methods.add(name='__contains__')
    def m_contains(self, key: ProxySort, ctx: 'Context') -> 'BoolSort':
        return types.bool.val(False, ctx=ctx)

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(other, types.dict):
            return types.bool.val(False, ctx=ctx)
        if isinstance(other, UntypedDictSort):
            return types.bool.val(True, ctx=ctx)

        empty = z3.K(dom=other.expr.domain(), v=other.expr.default())
        expr = other.expr == empty
        return types.bool(expr=expr)
