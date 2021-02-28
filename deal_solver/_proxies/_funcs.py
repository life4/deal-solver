# stdlib
import typing
from random import choices
from string import ascii_letters

# external
import z3

# app
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._proxy import ProxySort


T = typing.TypeVar('T', bound='ProxySort')


def unwrap(obj: 'ProxySort') -> z3.Z3PPObject:
    # app
    from ._proxy import ProxySort

    if not isinstance(obj, ProxySort):
        return obj
    expr = obj.expr
    if expr is None:
        return obj.make_empty_expr(z3.IntSort())
    return expr


def wrap(expr) -> 'ProxySort':
    # app
    from ._float import FPSort, RealSort
    from ._proxy import ProxySort

    if isinstance(expr, ProxySort):
        return expr
    if z3.is_bool(expr):
        return registry.bool(expr=expr)
    if z3.is_string(expr):
        return registry.str(expr=expr)
    if z3.is_seq(expr):
        return registry.list(expr=expr)
    if z3.is_array(expr):
        return registry.set(expr=expr)
    if z3.is_fp(expr):
        return FPSort.wrap(expr)
    if z3.is_real(expr):
        return RealSort.wrap(expr=expr)
    if z3.is_int(expr):
        return registry.int(expr=expr)
    return expr


def if_expr(
    test: typing.Any,
    val_then: T,
    val_else: T,
    ctx: typing.Optional[z3.Context] = None,
) -> T:
    expr = z3.If(
        wrap(test).as_bool.expr,
        unwrap(val_then),
        unwrap(val_else),
        ctx=ctx,
    )
    return wrap(expr)  # type: ignore


def random_name(prefix: str = 'v') -> str:
    suffix = ''.join(choices(ascii_letters, k=20))
    return prefix + '__' + suffix


def switch(*cases: typing.Tuple[typing.Any, T], default) -> T:
    result = default
    for cond, then in reversed(cases):
        result = if_expr(cond, then, result)
    return result


def and_expr(*args: 'ProxySort') -> 'BoolSort':
    return registry.bool(z3.And(*[arg.as_bool.expr for arg in args]))


def or_expr(*args: 'ProxySort') -> 'BoolSort':
    return registry.bool(z3.Or(*[wrap(arg).as_bool.expr for arg in args]))


def not_expr(cond: 'ProxySort') -> 'BoolSort':
    return registry.bool(z3.Not(wrap(cond).as_bool.expr))
