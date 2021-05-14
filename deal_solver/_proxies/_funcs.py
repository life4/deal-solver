# stdlib
import typing
from random import choices
from string import ascii_letters

# external
import z3

# app
from .._context import Context
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._proxy import ProxySort


T = typing.TypeVar('T', bound='ProxySort')


def unwrap(obj: 'ProxySort') -> z3.ExprRef:
    # app
    from ._proxy import ProxySort

    if not isinstance(obj, ProxySort):
        return obj
    return obj.expr


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
    ctx: Context,
) -> T:
    expr = z3.If(
        wrap(test).m_bool(ctx=ctx).expr,
        unwrap(val_then),
        unwrap(val_else),
        ctx=ctx.z3_ctx,
    )
    return wrap(expr)  # type: ignore


def random_name(prefix: str = 'v') -> str:
    suffix = ''.join(choices(ascii_letters, k=20))
    return prefix + '__' + suffix


def switch(*cases: typing.Tuple[typing.Any, T], default, ctx: Context) -> T:
    result = default
    for cond, then in reversed(cases):
        result = if_expr(cond, then, result, ctx=ctx)
    return result


def and_expr(*args: 'ProxySort', ctx: Context) -> 'BoolSort':
    return registry.bool(z3.And(*[arg.m_bool(ctx=ctx).expr for arg in args]))


def or_expr(*args: 'ProxySort', ctx: Context) -> 'BoolSort':
    return registry.bool(z3.Or(*[wrap(arg).m_bool(ctx=ctx).expr for arg in args]))


def not_expr(cond: 'ProxySort', *, ctx: Context) -> 'BoolSort':
    return registry.bool(z3.Not(wrap(cond).m_bool(ctx=ctx).expr))
