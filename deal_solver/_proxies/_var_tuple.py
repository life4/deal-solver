# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import random_name, unwrap, wrap
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort


T = typing.TypeVar('T', bound='VarTupleSort')


@registry.add
class VarTupleSort(ProxySort):
    expr: typing.Optional[z3.SeqRef]
    type_name = 'tuple'
    methods = ProxySort.methods.copy()

    def __init__(self, expr) -> None:
        if expr is not None:
            assert z3.is_seq(expr)
            assert not z3.is_string(expr)
        self.expr = expr

    def sort(self) -> z3.SeqSortRef:
        if self.expr is None:
            return z3.SeqSort(z3.IntSort())
        return self.expr.sort()

    @classmethod
    def from_items(cls: typing.Type[T], values: typing.List[ProxySort], ctx: 'Context') -> T:
        if not values:
            return cls(expr=None)
        items = cls.make_empty_expr(sort=unwrap(values[0]).sort())
        for value in values:
            item = z3.Unit(unwrap(value))
            items = z3.Concat(items, item)
        return cls(expr=items)

    @classmethod
    def make_empty(cls: typing.Type[T], sort: z3.SortRef = None) -> T:
        expr = None
        if sort is not None:
            expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @staticmethod
    def make_empty_expr(sort):
        return z3.Empty(z3.SeqSort(sort))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        if self.expr is None:
            return registry.bool.val(False)
        expr = z3.Length(self.expr) != z3.IntVal(0)
        return registry.bool(expr=expr)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        # app
        from .._context import ExceptionInfo
        if self.expr is None:
            msg = '{} index out of range'.format(self.type_name)
            ctx.add_exception(IndexError, msg)
            return self
        ctx.exceptions.add(ExceptionInfo(
            name='IndexError',
            names={'IndexError', 'LookupError', 'Exception', 'BaseException'},
            cond=registry.bool(expr=index.expr >= z3.Length(self.expr)),
            message='{} index out of range'.format(self.type_name),
        ))
        return wrap(self.expr[index.expr])

    def get_slice(self, start: 'ProxySort', stop: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if self.expr is None:
            return self
        start_expr = unwrap(start)
        stop_expr = unwrap(stop)
        proxy = type(self)
        return proxy(z3.SubSeq(
            s=self.expr,
            offset=start_expr,
            length=stop_expr - start_expr,
        ))

    @methods.add(name='__contains__')
    def m_contains(self, item: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        if self.expr is None:
            return registry.bool.val(False)
        if not self.expr.sort().basis().eq(item.expr.sort()):
            return registry.bool.val(False)
        self._ensure(item)
        unit = z3.Unit(unwrap(item))
        return registry.bool(expr=z3.Contains(self.expr, unit))

    @methods.add(name='index')
    def r_index(self, other: 'ProxySort', start: 'ProxySort' = None, *, ctx: 'Context') -> 'IntSort':
        if start is None:
            start = z3.IntVal(0)
        unit = z3.Unit(unwrap(other))
        return registry.int(expr=z3.IndexOf(self.expr, unit, unwrap(start)))

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        if self.expr is None:
            return registry.int(expr=z3.IntVal(0))
        return registry.int(expr=z3.Length(self.expr))

    @methods.add(name='count')
    def r_count(self, item: 'ProxySort', ctx: 'Context') -> 'IntSort':
        if self.expr is None:
            return registry.int(expr=z3.IntVal(0))
        item_expr = unwrap(item)
        f = z3.RecFunction(
            random_name('list_count'),
            z3.IntSort(), z3.IntSort(),
        )
        i = z3.Int(random_name('index'))
        one = z3.IntVal(1)
        zero = z3.IntVal(0)
        z3.RecAddDefinition(f, i, z3.If(
            i < zero,
            zero,
            f(i - one) + z3.If(self.expr[i] == item_expr, one, zero),
        ))
        result = f(z3.Length(self.expr) - one)
        return registry.int(result)

    @methods.add(name='__add__')
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if type(other) is not type(self):
            msg = 'can only concatenate {s} (not "{o}") to {s}'
            msg = msg.format(s=self.type_name, o=other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    @methods.add(name='__mul__')
    def m_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.int):
            msg = "can't multiply sequence by non-int of type '{}'"
            msg = msg.format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        raise UnsupportedError('cannot multiply list')

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='+', ctx=ctx)

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='-', ctx=ctx)

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='~', ctx=ctx)
