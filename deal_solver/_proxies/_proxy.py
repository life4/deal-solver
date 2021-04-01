# stdlib
import operator
import typing

# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap, wrap


if typing.TYPE_CHECKING:
    # app
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
        self.expr = expr

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

    @property
    def length(self) -> 'IntSort':
        """len(self)
        """
        raise UnsupportedError('{}.__len__ is not defined'.format(self.type_name))

    def get_item(self, item) -> 'ProxySort':
        """self[item]
        """
        raise UnsupportedError('{}.__getitem__ is not defined'.format(self.type_name))

    def contains(self, item) -> 'BoolSort':
        """item in self
        """
        raise UnsupportedError('{}.__contains__ is not defined'.format(self.type_name))

    def sort(self):
        return self.expr.sort()

    def _binary_op(self, other: 'ProxySort', handler: typing.Callable):
        self._ensure(other, seq=True)
        return handler(self.expr, unwrap(other))

    # comparison

    def _comp_op(self, other: 'ProxySort', handler: typing.Callable) -> 'BoolSort':
        # app
        from ._bool import BoolSort
        expr = self._binary_op(other=other, handler=handler)
        return BoolSort(expr=expr)

    def is_eq(self, other: 'ProxySort') -> 'BoolSort':
        """self == other
        """
        return self._comp_op(other=other, handler=operator.__eq__)

    def is_ne(self, other: 'ProxySort') -> 'BoolSort':
        """self != other
        """
        return self._comp_op(other=other, handler=operator.__ne__)

    def is_lt(self, other: 'ProxySort') -> 'BoolSort':
        """self < other
        """
        return self._comp_op(other=other, handler=operator.__lt__)

    def is_le(self, other: 'ProxySort') -> 'BoolSort':
        """self <= other
        """
        return self._comp_op(other=other, handler=operator.__le__)

    def is_gt(self, other: 'ProxySort') -> 'BoolSort':
        """self > other
        """
        return self._comp_op(other=other, handler=operator.__gt__)

    def is_ge(self, other: 'ProxySort') -> 'BoolSort':
        """self >= other
        """
        return self._comp_op(other=other, handler=operator.__ge__)

    def is_in(self, other: 'ProxySort') -> 'BoolSort':
        """self in other
        """
        return other.contains(self)

    # unary operations

    def as_negative(self: T) -> T:
        """-self
        """
        cls = type(self)
        return cls(expr=-self.expr)

    def as_positive(self: T) -> T:
        """+self
        """
        cls = type(self)
        return cls(expr=+self.expr)

    def as_inverted(self: T) -> T:
        """~self
        """
        raise UnsupportedError('{}.__invert__ is not defined'.format(self.type_name))

    # math binary operations

    def _math_op(self, other: 'ProxySort', handler: typing.Callable) -> 'ProxySort':
        return wrap(self._binary_op(other=other, handler=handler))

    def __add__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__add__)

    def __sub__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__sub__)

    def __mul__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__mul__)

    def __truediv__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__truediv__)

    def __floordiv__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__floordiv__)

    def __mod__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__mod__)

    def __pow__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__pow__)

    def __matmul__(self, other: 'ProxySort') -> 'ProxySort':
        return self._math_op(other=other, handler=operator.__matmul__)

    # bitwise binary operations

    def _bitwise_op(self: T, other: 'ProxySort', handler: typing.Callable):
        raise UnsupportedError(self.type_name, 'does not support bitwise operations')

    def __and__(self: T, other: 'ProxySort') -> T:
        return self._bitwise_op(other=other, handler=operator.__and__)

    def __or__(self: T, other: 'ProxySort') -> T:
        return self._bitwise_op(other=other, handler=operator.__or__)

    def __xor__(self: T, other: 'ProxySort') -> T:
        return self._bitwise_op(other=other, handler=operator.__xor__)

    def __lshift__(self: T, other: 'ProxySort') -> T:
        return self._bitwise_op(other=other, handler=operator.__lshift__)

    def __rshift__(self: T, other: 'ProxySort') -> T:
        return self._bitwise_op(other=other, handler=operator.__rshift__)
