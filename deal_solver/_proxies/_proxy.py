import operator
import typing

import z3

from .._exceptions import UnsupportedError
from ._methods import Methods
from ._type_factory import TypeFactory


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort
    from ._float import FloatSort, FPSort, RealSort
    from ._int import IntSort
    from ._str import StrSort


T = typing.TypeVar('T', bound='ProxySort')


class ProxySort:
    module_name: str = 'builtins'
    type_name: str
    expr: z3.ExprRef
    methods: 'Methods' = Methods()

    @staticmethod
    def make_empty_expr(sort):
        raise NotImplementedError

    def sort(self) -> z3.SortRef:
        return self.expr.sort()

    def __init__(self, expr) -> None:
        raise NotImplementedError

    @property
    def factory(self) -> TypeFactory:
        raise NotImplementedError

    @classmethod
    def var(cls, *, name: str, ctx: z3.Context) -> 'ProxySort':
        raise NotImplementedError

    @property
    def is_real(self) -> bool:
        return False

    @property
    def is_fp(self) -> bool:
        return False

    @methods.add(name='__getattr__')
    def m_getattr(self, name: str, ctx: 'Context') -> 'ProxySort':
        """self.name
        """
        method = self.methods.get(name)
        if method is None:
            msg = "'{}' object has no attribute '{}'"
            msg = msg.format(self.type_name, name)
            ctx.add_exception(AttributeError, msg)
            return self
        result = method.with_obj(self)
        if result.prop:
            return result.m_call(ctx=ctx)
        return result

    @methods.add(name='__bool__')
    def m_bool(self, ctx: 'Context') -> 'BoolSort':
        """bool(self)
        """
        from ._registry import types
        return types.bool.val(True, ctx=ctx)

    @methods.add(name='__abs__')
    def m_abs(self, ctx: 'Context') -> 'ProxySort':
        """abs(self)
        """
        msg = "bad operand type for abs(): '{}'".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    @methods.add(name='__int__')
    def m_int(self, ctx: 'Context') -> 'IntSort':
        """int(self)
        """
        raise UnsupportedError('cannot convert {} to int'.format(self.type_name))

    @methods.add(name='__str__')
    def m_str(self, ctx: 'Context') -> 'StrSort':
        """str(self)
        """
        raise UnsupportedError('cannot convert {} to str'.format(self.type_name))

    @methods.add(name='__float__')
    def m_float(self, ctx: 'Context') -> 'FloatSort':
        """float(self)
        """
        raise UnsupportedError('cannot convert {} to float'.format(self.type_name))

    def m_real(self, ctx: 'Context') -> 'RealSort':
        raise NotImplementedError

    def m_fp(self, ctx: 'Context') -> 'FPSort':
        raise NotImplementedError

    @methods.add(name='__call__')
    def m_call(self, *args, ctx: 'Context', **kwargs) -> 'ProxySort':
        """self(*args, **kwargs)
        """
        msg = "'{}' object is not callable".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    @methods.add(name='__len__')
    def m_len(self, ctx: 'Context') -> 'IntSort':
        """len(self)
        """
        from ._registry import types
        msg = "object of type '{}' has no len()".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return types.int.val(0, ctx=ctx)

    @methods.add(name='__getitem__')
    def m_getitem(self, item: 'ProxySort', ctx: 'Context') -> 'ProxySort':
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

    @methods.add(name='__setitem__')
    def m_setitem(self, key: 'ProxySort', value: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self[key] = value
        """
        msg = "'{}' object does not support item assignment"
        msg = msg.format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return self

    @methods.add(name='__contains__')
    def m_contains(self, item, ctx: 'Context') -> 'BoolSort':
        """item in self
        """
        from ._registry import types
        msg = "argument of type '{}' is not iterable".format(self.type_name)
        ctx.add_exception(TypeError, msg)
        return types.bool.val(False, ctx=ctx)

    def _binary_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context'):
        return handler(self.expr, other.expr)

    # comparison

    def _comp_op(self, other: 'ProxySort', handler: typing.Callable, ctx: 'Context') -> 'BoolSort':
        from ._bool import BoolSort
        expr = self._binary_op(other=other, handler=handler, ctx=ctx)
        return BoolSort(expr=expr)

    @methods.add(name='__eq__')
    def m_eq(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self == other
        """
        return self._comp_op(other=other, handler=operator.__eq__, ctx=ctx)

    @methods.add(name='__ne__')
    def m_ne(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self != other
        """
        from ._bool import BoolSort
        expr = self.m_eq(other, ctx=ctx).expr
        return BoolSort(expr=z3.Not(expr))

    @methods.add(name='__lt__')
    def m_lt(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self < other
        """
        return self._comp_op(other=other, handler=operator.__lt__, ctx=ctx)

    @methods.add(name='__le__')
    def m_le(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self <= other
        """
        return self._comp_op(other=other, handler=operator.__le__, ctx=ctx)

    @methods.add(name='__gt__')
    def m_gt(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self > other
        """
        return self._comp_op(other=other, handler=operator.__gt__, ctx=ctx)

    @methods.add(name='__ge__')
    def m_ge(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self >= other
        """
        return self._comp_op(other=other, handler=operator.__ge__, ctx=ctx)

    @methods.add(name='in')
    def m_in(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self in other
        """
        return other.m_contains(self, ctx=ctx)

    @methods.add(name='not in')
    def m_not_in(self, other: 'ProxySort', ctx: 'Context') -> 'BoolSort':
        """self in other
        """
        return other.m_contains(self, ctx=ctx).m_not(ctx=ctx)

    # unary operations

    @methods.add(name='__neg__')
    def m_neg(self, ctx: 'Context') -> 'ProxySort':
        """-self
        """
        cls = type(self)
        return cls(expr=-self.expr)

    @methods.add(name='__pos__')
    def m_pos(self, ctx: 'Context') -> 'ProxySort':
        """+self
        """
        cls = type(self)
        return cls(expr=+self.expr)

    @methods.add(name='__inv__')
    def m_inv(self, ctx: 'Context') -> 'ProxySort':
        """~self
        """
        return self._bad_un_op(op='~', ctx=ctx)

    @methods.add(name='not')
    def m_not(self, ctx: 'Context') -> 'BoolSort':
        """not self
        """
        from ._bool import BoolSort
        expr = self.m_bool(ctx=ctx).expr
        return BoolSort(expr=z3.Not(expr, ctx=ctx.z3_ctx))

    # math binary operations

    @methods.add(name='__add__')
    def m_add(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self + other
        """
        return self._bad_bin_op(other, op='+', ctx=ctx)

    @methods.add(name='__sub__')
    def m_sub(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self - other
        """
        return self._bad_bin_op(other, op='-', ctx=ctx)

    @methods.add(name='__mul__')
    def m_mul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self * other
        """
        return self._bad_bin_op(other, op='*', ctx=ctx)

    @methods.add(name='__truediv__')
    def m_truediv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self / other
        """
        return self._bad_bin_op(other, op='/', ctx=ctx)

    @methods.add(name='__floordiv__')
    def m_floordiv(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self // other
        """
        return self._bad_bin_op(other, op='//', ctx=ctx)

    @methods.add(name='__mod__')
    def m_mod(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self % other
        """
        return self._bad_bin_op(other, op='%', ctx=ctx)

    @methods.add(name='__pow__')
    def m_pow(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self ** other
        """
        return self._bad_bin_op(other, op='** or pow()', ctx=ctx)

    @methods.add(name='__matmul__')
    def m_matmul(self, other: 'ProxySort', ctx: 'Context') -> 'ProxySort':
        """self @ other
        """
        return self._bad_bin_op(other, op='@', ctx=ctx)

    # bitwise binary operations

    @methods.add(name='__and__')
    def m_and(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self & other
        """
        return self._bad_bin_op(other, op='&', ctx=ctx)

    @methods.add(name='__or__')
    def m_or(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self | other
        """
        return self._bad_bin_op(other, op='|', ctx=ctx)

    @methods.add(name='__xor__')
    def m_xor(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self ^ other
        """
        return self._bad_bin_op(other, op='^', ctx=ctx)

    @methods.add(name='__lshift__')
    def m_lshift(self: T, other: 'ProxySort', ctx: 'Context') -> T:
        """self << other
        """
        return self._bad_bin_op(other, op='<<', ctx=ctx)

    @methods.add(name='__rshift__')
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
