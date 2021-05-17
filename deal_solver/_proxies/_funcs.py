import typing
from random import choices
from string import ascii_letters

import z3

from .._context import Context
from ._registry import types


if typing.TYPE_CHECKING:
    from ._bool import BoolSort
    from ._proxy import ProxySort


T = typing.TypeVar('T', bound='ProxySort')


def wrap(expr) -> 'ProxySort':
    from ._float import FPSort, RealSort
    from ._proxy import ProxySort

    if isinstance(expr, ProxySort):
        return expr
    if z3.is_bool(expr):
        return types.bool(expr=expr)
    if z3.is_string(expr):
        return types.str(expr=expr)
    if z3.is_seq(expr):
        return types.list(expr=expr)
    if z3.is_fp(expr):
        return FPSort.wrap(expr)
    if z3.is_real(expr):
        return RealSort.wrap(expr=expr)
    if z3.is_int(expr):
        return types.int(expr=expr)
    return expr


def if_expr(
    test: 'ProxySort',
    val_then: T,
    val_else: T,
    ctx: Context,
) -> T:
    expr = z3.If(
        test.m_bool(ctx=ctx).expr,
        val_then.expr,
        val_else.expr,
        ctx=ctx.z3_ctx,
    )
    return type(val_then)(expr)


def random_name(prefix: str = 'v') -> str:
    suffix = ''.join(choices(ascii_letters, k=20))
    return prefix + '__' + suffix


def switch(*cases: typing.Tuple['ProxySort', T], default, ctx: Context) -> T:
    result = default
    for cond, then in reversed(cases):
        result = if_expr(cond, then, result, ctx=ctx)
    return result


def and_expr(*args: 'ProxySort', ctx: Context) -> 'BoolSort':
    return types.bool(z3.And(*[arg.m_bool(ctx=ctx).expr for arg in args]))


def or_expr(*args: 'ProxySort', ctx: Context) -> 'BoolSort':
    return types.bool(z3.Or(*[arg.m_bool(ctx=ctx).expr for arg in args]))


def not_expr(cond: 'ProxySort', *, ctx: Context) -> 'BoolSort':
    return types.bool(z3.Not(cond.m_bool(ctx=ctx).expr))
