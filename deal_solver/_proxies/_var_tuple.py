import operator
import typing

import z3

from .._exceptions import UnsupportedError
from ._funcs import random_name, wrap
from ._proxy import ProxySort
from ._registry import types
from ._type_info import TypeInfo


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort
    from ._int import IntSort


T = typing.TypeVar('T', bound='VarTupleSort')


@types.add
class VarTupleSort(ProxySort):
    type_name = 'tuple'
    methods = ProxySort.methods.copy()

    expr: z3.SeqRef
    subtypes: typing.Tuple[TypeInfo, ...]

    def __init__(self, expr, subtypes=()) -> None:
        assert len(subtypes) <= 1
        assert z3.is_seq(expr)
        assert not z3.is_string(expr)
        self.expr = expr
        self.subtypes = subtypes

    def sort(self) -> z3.SeqSortRef:
        return self.expr.sort()

    def get_type_info(self, ctx: 'Context') -> TypeInfo:
        sort = self.expr.sort().basis()
        expr = self.make_empty_expr(sort)
        empty = self.evolve(expr=expr)
        return TypeInfo(
            type=type(self),
            default=empty,
            subtypes=self.subtypes,
        )

    @classmethod
    def from_items(cls: typing.Type[T], values: typing.List[ProxySort], ctx: 'Context') -> T:
        items = cls.make_empty_expr(sort=values[0].expr.sort())
        for value in values:
            item = z3.Unit(value.expr)
            items = z3.Concat(items, item)
        value_type = values[0].get_type_info(ctx=ctx)
        return cls(expr=items, subtypes=(value_type,))

    @staticmethod
    def make_empty_expr(sort):
        return z3.Empty(z3.SeqSort(sort))

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        expr = z3.Length(self.expr) != z3.IntVal(0)
        return types.bool(expr=expr)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: ProxySort, ctx: 'Context') -> ProxySort:
        from .._context import ExceptionInfo
        ctx.exceptions.add(ExceptionInfo(
            name='IndexError',
            names={'IndexError', 'LookupError', 'Exception', 'BaseException'},
            cond=types.bool(expr=index.expr >= z3.Length(self.expr)),
            message='{} index out of range'.format(self.type_name),
        ))
        expr = self.expr[index.expr]
        if self.subtypes:
            item = self.subtypes[0].wrap(expr)
        else:
            item = wrap(expr)
        return item

    def get_slice(self, start: ProxySort, stop: ProxySort, ctx: 'Context') -> ProxySort:
        start_expr = start.expr
        stop_expr = stop.expr
        proxy = type(self)
        return proxy(z3.SubSeq(
            s=self.expr,
            offset=start_expr,
            length=stop_expr - start_expr,
        ))

    @methods.add(name='__contains__')
    def m_contains(self, item: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not self.expr.sort().basis().eq(item.expr.sort()):
            return types.bool.val(False, ctx=ctx)
        unit = z3.Unit(item.expr)
        return types.bool(expr=z3.Contains(self.expr, unit))

    @methods.add(name='index')
    def r_index(self, other: ProxySort, start: ProxySort = None, *, ctx: 'Context') -> 'IntSort':
        if start is None:
            start = types.int(z3.IntVal(0))
        unit = z3.Unit(other.expr)
        return types.int(expr=z3.IndexOf(self.expr, unit, start.expr))

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        return types.int(expr=z3.Length(self.expr))

    @methods.add(name='count')
    def r_count(self, item: ProxySort, ctx: 'Context') -> 'IntSort':
        item_expr = item.expr
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
        return types.int(result)

    @methods.add(name='__add__')
    def m_add(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if self.type_name != other.type_name:
            msg = 'can only concatenate {s} (not "{o}") to {s}'
            msg = msg.format(s=self.type_name, o=other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    @methods.add(name='__mul__')
    def m_mul(self, other: ProxySort, ctx: 'Context') -> ProxySort:
        if not isinstance(other, types.int):
            msg = "can't multiply sequence by non-int of type '{}'"
            msg = msg.format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        raise UnsupportedError('cannot multiply list')

    @methods.add(name='__eq__')
    def m_eq(self, other: ProxySort, ctx: 'Context') -> 'BoolSort':
        # type mismatch
        if not isinstance(other, types.tuple):
            return types.bool.val(False, ctx=ctx)
        # other is untyped
        if isinstance(other, UntypedVarTupleSort):
            empty = self.make_empty_expr(sort=self.sort().basis())
            expr = self.expr == empty
            return types.bool(expr=expr)
        return super().m_eq(other, ctx=ctx)

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='+', ctx=ctx)

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='-', ctx=ctx)

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'VarTupleSort':
        return self._bad_un_op(op='~', ctx=ctx)


class UntypedVarTupleSort(VarTupleSort):
    methods = VarTupleSort.methods.copy()
    subtypes = ()

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
        return types.bool.val(False, ctx=ctx)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: ProxySort, ctx: 'Context') -> ProxySort:
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
