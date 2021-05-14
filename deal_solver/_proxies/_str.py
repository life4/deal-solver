# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort
    from ._float import FloatSort
    from ._int import IntSort


@registry.add
class StrSort(ProxySort):
    type_name = 'str'
    methods = ProxySort.methods.copy()
    expr: z3.SeqRef

    def __init__(self, expr) -> None:
        assert z3.is_string(expr)
        self.expr = expr

    @methods.add(name='__int__')
    def m_int(self, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        return registry.int(expr=z3.StrToInt(self.expr))

    @methods.add(name='__str__')
    def m_str(self, ctx: 'Context') -> 'StrSort':
        return self

    @methods.add(name='__float__')
    def m_float(self, ctx: 'Context') -> 'FloatSort':
        assert self.expr is not None
        if z3.is_string_value(self.expr):
            val = float(self.expr.as_string())
            return registry.float.val(val)
        raise UnsupportedError('cannot convert str to float')

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        assert self.expr is not None
        expr = self.expr != z3.Empty(z3.StringSort())
        return registry.bool(expr=expr)

    @methods.add(name='__getitem__')
    def m_getitem(self, index: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        # TODO: emit IndexError
        expr = z3.SubString(
            s=self.expr,
            offset=index.expr,
            length=z3.IntVal(1, ctx=ctx.z3_ctx),
        )
        return registry.str(expr=expr)

    @methods.add(name='__contains__')
    def m_contains(self, item: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        if not isinstance(item, registry.str):
            msg = "'in <string>' requires string as left operand, not {}"
            msg = msg.format(item.type_name)
            ctx.add_exception(TypeError, msg)
            return registry.bool.val(True)
        assert self.expr is not None
        expr = z3.Contains(self.expr, item.expr)
        return registry.bool(expr=expr)

    @methods.add(name='startswith')
    def r_startswith(self, prefix: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.PrefixOf(prefix.expr, self.expr)
        return registry.bool(expr=expr)

    @methods.add(name='endswith')
    def r_endswith(self, suffix: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.SuffixOf(suffix.expr, self.expr)
        return registry.bool(expr=expr)

    @methods.add(name='index')
    def r_index(self, other: 'ProxySort', start: 'ProxySort' = None, *, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        if start is None:
            start = registry.int.val(0)
        # TODO: emit IndexError
        return registry.int(expr=z3.IndexOf(self.expr, other.expr, start.expr))

    @methods.add(name='find')
    def r_find(self, other: 'ProxySort', start: 'ProxySort' = None, *, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        if start is None:
            start = registry.int.val(0)
        expr = z3.If(
            z3.Contains(
                z3.SubString(self.expr, offset=start.expr, length=z3.Length(self.expr)),
                other.expr,
            ),
            z3.IndexOf(self.expr, other.expr, start.expr),
            z3.IntVal(-1, ctx=ctx.z3_ctx),
        )
        return registry.int(expr=expr)

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        return registry.int(expr=z3.Length(self.expr))

    @methods.add(name='__add__')
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.str):
            msg = 'can only concatenate str (not "{}") to {}'
            msg = msg.format(other.type_name, self.type_name)
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
        raise UnsupportedError('cannot multiply str')

    @methods.add(name='__mod__')
    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'StrSort':
        msg = 'not all arguments converted during string formatting'
        ctx.add_exception(TypeError, msg)
        return self

    @methods.add(name='__sub__')
    def m_sub(self, other: 'ProxySort', ctx: 'Context') -> 'StrSort':
        return self._bad_bin_op(other, op='-', ctx=ctx)

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='+', ctx=ctx)

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='-', ctx=ctx)

    @methods.add(name='capitalize')
    @methods.add(name='casefold')
    @methods.add(name='center')
    @methods.add(name='count')
    @methods.add(name='encode')
    @methods.add(name='expandtabs')
    @methods.add(name='format')
    @methods.add(name='format_map')
    @methods.add(name='isalnum')
    @methods.add(name='isalpha')
    @methods.add(name='isascii')
    @methods.add(name='isdecimal')
    @methods.add(name='isdigit')
    @methods.add(name='isidentifier')
    @methods.add(name='islower')
    @methods.add(name='isnumeric')
    @methods.add(name='isprintable')
    @methods.add(name='isspace')
    @methods.add(name='istitle')
    @methods.add(name='isupper')
    @methods.add(name='join')
    @methods.add(name='ljust')
    @methods.add(name='lower')
    @methods.add(name='lstrip')
    @methods.add(name='maketrans')
    @methods.add(name='partition')
    @methods.add(name='removeprefix')
    @methods.add(name='removesuffix')
    @methods.add(name='replace')
    @methods.add(name='rfind')
    @methods.add(name='rindex')
    @methods.add(name='rjust')
    @methods.add(name='rpartition')
    @methods.add(name='rsplit')
    @methods.add(name='rstrip')
    @methods.add(name='split')
    @methods.add(name='splitlines')
    @methods.add(name='strip')
    @methods.add(name='swapcase')
    @methods.add(name='title')
    @methods.add(name='translate')
    @methods.add(name='upper')
    @methods.add(name='zfill')
    def unsupported(self, *args, **kwargs):
        msg = 'unsupported attribute for type {}'.format(self.type_name)
        raise UnsupportedError(msg)
