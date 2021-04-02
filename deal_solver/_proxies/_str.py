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
    from ._bool import BoolSort
    from ._float import FloatSort
    from ._int import IntSort
    from .._context import Context


@registry.add
class StrSort(ProxySort):
    type_name = 'str'

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

    def contains(self, item: 'ProxySort') -> 'BoolSort':
        assert self.expr is not None
        self._ensure(item)
        expr = z3.Contains(self.expr, unwrap(item))
        return registry.bool(expr=expr)

    def startswith(self, prefix: 'ProxySort') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.PrefixOf(unwrap(prefix), self.expr)
        return registry.bool(expr=expr)

    def endswith(self, suffix: 'ProxySort') -> 'BoolSort':
        assert self.expr is not None
        expr = z3.SuffixOf(unwrap(suffix), self.expr)
        return registry.bool(expr=expr)

    def index(self, other: 'ProxySort', start=None) -> 'IntSort':
        assert self.expr is not None
        if start is None:
            start = z3.IntVal(0)
        return registry.int(expr=z3.IndexOf(self.expr, unwrap(other), unwrap(start)))

    @property
    def length(self) -> 'IntSort':
        assert self.expr is not None
        return registry.int(expr=z3.Length(self.expr))

    def op_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.str):
            return self._bad_bin_op(other, op='+', ctx=ctx)
        return self._math_op(other=other, handler=operator.__add__, ctx=ctx)

    def op_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        if not isinstance(other, registry.int):
            return self._bad_bin_op(other, op='*', ctx=ctx)
        raise UnsupportedError('cannot multiply str')

    def op_sub(self, other: 'ProxySort', ctx: 'Context') -> 'StrSort':
        return self._bad_bin_op(other, op='-', ctx=ctx)

    def as_positive(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='+', ctx=ctx)

    def as_negative(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='-', ctx=ctx)

    def as_inverted(self, ctx: 'Context') -> 'StrSort':
        return self._bad_un_op(op='~', ctx=ctx)
