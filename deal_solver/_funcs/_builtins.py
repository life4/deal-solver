# external
import z3

# app
from .._context import Context, ExceptionInfo
from .._proxies import (
    BoolSort, IntSort, ProxySort, SetSort, UntypedSetSort, StrSort, if_expr, random_name, unwrap, wrap,
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
        return if_expr(a.m_lt(b, ctx=ctx), a, b, ctx=ctx)

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
        return if_expr(a.m_gt(b, ctx=ctx), a, b, ctx=ctx)

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


@register('builtins.ord')
def builtins_ord(val: ProxySort, ctx: Context, **kwargs) -> IntSort:
    if not isinstance(val, StrSort):
        msg = 'ord() expected string of length 1, but {} found'
        msg = msg .format(val.type_name)
        ctx.add_exception(TypeError, msg)
        return IntSort.val(0)
    ctx.exceptions.add(ExceptionInfo(
        name='TypeError',
        names={'TypeError', 'Exception', 'BaseException'},
        cond=val.m_len(ctx=ctx).m_ne(IntSort.val(1), ctx=ctx),
        message='ord() expected a character, but string of length N found',
    ))
    bv = z3.BitVec(random_name('ord_bv'), 8)
    ctx.given.add(BoolSort(z3.Unit(bv) == unwrap(val)))
    return IntSort(z3.BV2Int(bv))


@register('builtins.abs')
def builtins_abs(a: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    return a.abs


@register('builtins.len')
def builtins_len(items: ProxySort, ctx: 'Context', **kwargs) -> IntSort:
    return items.m_len(ctx=ctx)


@register('builtins.int')
def builtins_int(a: ProxySort, *, ctx: Context, **kwargs) -> ProxySort:
    return a.m_int(ctx=ctx)


@register('builtins.float')
def builtins_float(a: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    return a.m_float(ctx=ctx)


@register('builtins.str')
def builtins_str(obj: ProxySort, ctx: Context, **kwargs) -> StrSort:
    return obj.m_str(ctx=ctx)


@register('builtins.bool')
def builtins_bool(obj: ProxySort, ctx: Context, **kwargs) -> BoolSort:
    return obj.m_bool(ctx=ctx)


@register('builtins.set')
def builtins_set(**kwargs) -> SetSort:
    return UntypedSetSort()
