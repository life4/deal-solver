# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap, wrap, not_expr


if typing.TYPE_CHECKING:
    # app
    from .._context import Context
    from ._bool import BoolSort
    from ._float import FloatSort, FPSort, RealSort
    from ._int import IntSort
    from ._str import StrSort


T = typing.TypeVar('T', bound='ProxySort')


class ProxySort:
    type_name: str
    expr: z3.Z3PPObject

    @staticmethod
    def make_empty_expr(sort):
        raise NotImplementedError

    def _ensure(self, item, seq=False) -> None:
        """
        Sometimes, the subtype for sequences is not known in advance.
        In that case, we set `expr=None`.

        What `_ensure` does is it takes another item or sequence,
        extracts type from it, and sets the type for the current sequence
        to match the another one. For example, if `a` is an empty list,
        operation `a.append(1)` will set the subtype of `a` to `int`.
        """
        if self.expr is not None:
            return
        item = unwrap(item)
        if item is None:
            sort = z3.IntSort()
        else:
            sort = item.sort()

        if seq:
            if isinstance(sort, z3.ArraySortRef):
                sort = sort.domain()
            elif isinstance(sort, z3.SeqSortRef):
                sort = sort.basis()

        self.expr = self.make_empty_expr(sort)

    def __init__(self, expr) -> None:
        raise NotImplementedError

    @property
    def is_real(self) -> bool:
        return False

    @property
    def is_fp(self) -> bool:
        return False

    # abstract methods

    @property
    def as_bool(self) -> 'BoolSort':
        """bool(self)
        """
        raise NotImplementedError

    @property
    def abs(self) -> 'ProxySort':
        """abs(self)
        """
        raise UnsupportedError('{}.__abs__ is not defined'.format(self.type_name))

    @property
    def as_int(self) -> 'IntSort':
        """int(self)
        """
        raise UnsupportedError('cannot convert {} to int'.format(self.type_name))

    @property
    def as_str(self) -> 'StrSort':
        """str(self)
        """
        raise UnsupportedError('cannot convert {} to str'.format(self.type_name))

    @property
    def as_float(self) -> 'FloatSort':
        """float(self)
        """
        raise UnsupportedError('cannot convert {} to float'.format(self.type_name))

    @property
    def as_real(self) -> 'RealSort':
        raise UnsupportedError('cannot convert {} to float'.format(self.type_name))

    @property
    def as_fp(self) -> 'FPSort':
        raise UnsupportedError('cannot convert {} to float'.format(self.type_name))

    def m_len(self, ctx: 'Context') -> 'IntSort':
        """len(self)
        """
        from ._registry import registry
        msg = "object of type '{}' has no len()".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return registry.int.val(0)

    def get_item(self, item, ctx: 'Context') -> 'ProxySort':
        """self[item]
        """
        msg = "'{}' object is not subscriptable"
        msg = msg.format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    def get_slice(self, start, stop, ctx: 'Context') -> 'ProxySort':
        """self[start:stop]
        """
        msg = "'{}' object is not subscriptable"
        msg = msg.format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    def m_contains(self, item, ctx: 'Context') -> 'BoolSort':
        """item in self
        """
        from ._registry import registry
        msg = "argument of type '{}' is not iterable".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return registry.bool.val(False)

    def _binary_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context'):
        self._ensure(other, seq=True)
        return handler(self.expr, unwrap(other))

    # comparison

    def _comp_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'BoolSort':
        # app
        from ._bool import BoolSort
        expr = self._binary_op(other=other, handler=handler, ctx=ctx)
        return BoolSort(expr=expr)

    def m_eq(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self == other
        """
        return self._comp_op(other=other, handler=operator.__eq__, ctx=ctx)

    def m_ne(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self != other
        """
        return self._comp_op(other=other, handler=operator.__ne__, ctx=ctx)

    def m_lt(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self < other
        """
        return self._comp_op(other=other, handler=operator.__lt__, ctx=ctx)

    def m_le(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self <= other
        """
        return self._comp_op(other=other, handler=operator.__le__, ctx=ctx)

    def m_gt(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self > other
        """
        return self._comp_op(other=other, handler=operator.__gt__, ctx=ctx)

    def m_ge(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self >= other
        """
        return self._comp_op(other=other, handler=operator.__ge__, ctx=ctx)

    def m_in(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self in other
        """
        return other.m_contains(self, ctx=ctx)

    def m_not_in(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self in other
        """
        return not_expr(other.m_contains(self, ctx=ctx))

    # unary operations

    def m_neg(self, ctx: 'Context') -> 'ProxySort':
        """-self
        """
        cls = type(self)
        return cls(expr=-self.expr)

    def m_pos(self, ctx: 'Context') -> 'ProxySort':
        """+self
        """
        cls = type(self)
        return cls(expr=+self.expr)

    def m_inv(self, ctx: 'Context') -> 'ProxySort':
        """~self
        """
        msg = "bad operand type for unary ~: '{}'"
        msg = msg.format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    # math binary operations

    def _math_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'ProxySort':
        return wrap(self._binary_op(other=other, handler=handler, ctx=ctx))

    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self + other
        """
        return self._bad_bin_op(other, op='+', ctx=ctx)

    def m_sub(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self - other
        """
        return self._bad_bin_op(other, op='-', ctx=ctx)

    def m_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self * other
        """
        return self._bad_bin_op(other, op='*', ctx=ctx)

    def m_truediv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self / other
        """
        return self._bad_bin_op(other, op='/', ctx=ctx)

    def m_floordiv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self // other
        """
        return self._bad_bin_op(other, op='//', ctx=ctx)

    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self % other
        """
        return self._bad_bin_op(other, op='%', ctx=ctx)

    def m_pow(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self ** other
        """
        return self._bad_bin_op(other, op='** or pow()', ctx=ctx)

    def m_matmul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self @ other
        """
        return self._bad_bin_op(other, op='@', ctx=ctx)

    # bitwise binary operations

    def m_and(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self & other
        """
        return self._bad_bin_op(other, op='&', ctx=ctx)

    def m_or(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self | other
        """
        return self._bad_bin_op(other, op='|', ctx=ctx)

    def m_xor(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self ^ other
        """
        return self._bad_bin_op(other, op='^', ctx=ctx)

    def m_lshift(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self << other
        """
        return self._bad_bin_op(other, op='<<', ctx=ctx)

    def m_rshift(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self >> other
        """
        return self._bad_bin_op(other, op='>>', ctx=ctx)

    # helpers for error messages in operations

    def _bad_bin_op(self: T, other: 'ProxySort', op: str, ctx: 'Context') -> T:
        msg = "unsupported operand type(s) for {}: '{}' and '{}'"
        msg = msg.format(op, self.type_name, other.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    def _bad_un_op(self: T, op: str, ctx: 'Context') -> T:
        msg = "bad operand type for unary {}: '{}'"
        msg = msg.format(op, self.type_name)
        ctx.add_exception(TypeError, msg)
        return self
