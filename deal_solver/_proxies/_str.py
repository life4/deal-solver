# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap
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

    def __init__(self, expr) -> None:
        assert z3.is_string(expr)
        self.expr = expr

    def _ensure(self, item, seq=False):
        pass

    @property
    def as_int(self) -> 'IntSort':
        assert self.expr is not None
        return registry.int(expr=z3.StrToInt(self.expr))

    @property
    def as_str(self) -> 'StrSort':
        return self

    @property
    def as_float(self) -> 'FloatSort':
        assert self.expr is not None
        if z3.is_string_value(self.expr):
            val = float(self.expr.as_string())
            return registry.float.val(val)
        raise UnsupportedError('cannot convert str to float')

    @property
    def as_bool(self) -> 'BoolSort':
        assert self.expr is not None
        expr = self.expr != z3.Empty(z3.StringSort())
        return registry.bool(expr=expr)

    def m_contains(self, item: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        if not isinstance(item, registry.str):
            msg = "'in <string>' requires string as left operand, not {}"
            msg = msg.format(item.type_name)
            ctx.add_exception(TypeError, msg)
            return registry.bool.val(True)
        assert self.expr is not None
        self._ensure(item)
        expr = z3.Contains(self.expr, unwrap(item))
        return registry.bool(expr=expr)

    @methods.add(name='startswith')
    def r_startswith(self, prefix: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.PrefixOf(unwrap(prefix), self.expr)
        return registry.bool(expr=expr)

    @methods.add(name='endswith')
    def r_endswith(self, suffix: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.SuffixOf(unwrap(suffix), self.expr)
        return registry.bool(expr=expr)

    @methods.add(name='index')
    def r_index(self, other: 'ProxySort', start=None, *, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        if start is None:
            start = z3.IntVal(0)
        return registry.int(expr=z3.IndexOf(self.expr, unwrap(other), unwrap(start)))

    def m_len(self, ctx: 'Context') -> 'IntSort':
        assert self.expr is not None
        return registry.int(expr=z3.Length(self.expr))

    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.str):
            msg = 'can only concatenate str (not "{}") to {}'
            msg = msg.format(other.type_name, self.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    def m_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.int):
            msg = "can't multiply sequence by non-int of type '{}'"
            msg = msg.format(other.type_name)
            ctx.add_exception(TypeError, msg)
            return self
        raise UnsupportedError('cannot multiply str')

    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'StrSort':
        msg = 'not all arguments converted during string formatting'
        ctx.add_exception(TypeError, msg)
        return self

    def m_sub(self, other: 'ProxySort', ctx: 'Context') -> 'StrSort':
        return self._bad_bin_op(other, op='-', ctx=ctx)

    def m_pos(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='+', ctx=ctx)

    def m_neg(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='-', ctx=ctx)

    def m_inv(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='~', ctx=ctx)
