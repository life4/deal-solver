# external
import z3

# app
from .._context import Context
from .._proxies import (
    BoolSort, IntSort, ProxySort, SetSort, StrSort, if_expr, random_name, unwrap, wrap,
)
from ._registry import register


@register('builtins.print')
def builtins_ignore(*args, **kwargs) -> None:
    return None


@register('builtins.sum')
def builtins_sum(items, ctx: Context, **kwargs) -> ProxySort:
    items = unwrap(items)
    f = z3.RecFunction(
        random_name('sum'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'), ctx=ctx.z3_ctx)
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        items[i] + f(i - one),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


# TODO: support more than 2 explicit arguments.
@register('builtins.min')
def builtins_min(a: ProxySort, b: ProxySort = None, *, ctx: Context, **kwargs) -> ProxySort:
    if b is not None:
        return if_expr(a < b, a, b)

    items = unwrap(a)
    f = z3.RecFunction(
        random_name('min'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'))
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] < f(i - one),
            items[i],
            f(i - one),
            ctx=ctx.z3_ctx,
        ),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


@register('builtins.max')
def builtins_max(a: ProxySort, b: ProxySort = None, *, ctx: Context, **kwargs) -> ProxySort:
    if b is not None:
        return if_expr(a > b, a, b, ctx=ctx.z3_ctx,)

    items = unwrap(a)
    f = z3.RecFunction(
        random_name('max'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'), ctx=ctx.z3_ctx)
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] > f(i - one),
            items[i],
            f(i - one),
            ctx=ctx.z3_ctx,
        ),
        ctx=ctx.z3_ctx,
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


@register('builtins.abs')
def builtins_abs(a: ProxySort, **kwargs) -> ProxySort:
    return a.abs


@register('builtins.len')
def builtins_len(items: ProxySort, **kwargs) -> IntSort:
    return items.length


@register('builtins.int')
def builtins_int(a: ProxySort, *, ctx: Context, **kwargs) -> ProxySort:
    return a.as_int


@register('builtins.float')
def builtins_float(a: ProxySort, **kwargs) -> ProxySort:
    return a.as_float


@register('builtins.str')
def builtins_str(obj: ProxySort, **kwargs) -> StrSort:
    return obj.as_str


@register('builtins.bool')
def builtins_bool(obj: ProxySort, **kwargs) -> BoolSort:
    return obj.as_bool


@register('builtins.set')
def builtins_set(**kwargs) -> SetSort:
    return SetSort.make_empty()
