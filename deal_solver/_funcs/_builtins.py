import z3

from .._context import Context
from .._exceptions import UnsupportedError
from .._proxies import (
    IntSort, ProxySort, StrSort, UntypedDictSort, UntypedListSort,
    UntypedSetSort, if_expr, random_name, types,
)
from ._registry import register


@register('builtins.print')
def builtins_ignore(*args, **kwargs) -> None:
    return None


@register('builtins.sum')
def builtins_sum(items: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    if not isinstance(items, (types.list, types.tuple)):
        raise UnsupportedError(f'cannot iterate over {items.type_name}')
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
        items.expr[zero],
        items.expr[i] + f(i - one),
    ))
    result = f(items.m_len(ctx=ctx).expr - one)
    return items.subtypes[0].wrap(result)


# TODO: support more than 2 explicit arguments.
@register('builtins.min')
def builtins_min(a: ProxySort, b: ProxySort = None, *, ctx: Context, **kwargs) -> ProxySort:
    if b is not None:
        return if_expr(a.m_lt(b, ctx=ctx), a, b, ctx=ctx)

    if not isinstance(a, (types.list, types.tuple)):
        raise UnsupportedError(f'cannot iterate over {a.type_name}')
    items = a.expr
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
    return a.subtypes[0].wrap(result)


@register('builtins.max')
def builtins_max(a: ProxySort, b: ProxySort = None, *, ctx: Context, **kwargs) -> ProxySort:
    if b is not None:
        return if_expr(a.m_gt(b, ctx=ctx), a, b, ctx=ctx)

    if not isinstance(a, (types.list, types.tuple)):
        raise UnsupportedError(f'cannot iterate over {a.type_name}')
    items = a.expr
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
    return a.subtypes[0].wrap(result)


@register('builtins.ord')
def builtins_ord(val: ProxySort, ctx: Context, **kwargs) -> IntSort:
    if not isinstance(val, StrSort):
        msg = 'ord() expected string of length 1, but {} found'
        msg = msg .format(val.type_name)
        ctx.add_exception(TypeError, msg)
        return types.int.val(0, ctx=ctx)
    ctx.add_exception(
        exc=TypeError,
        msg='ord() expected a character, but string of length N found',
        cond=val.m_len(ctx=ctx).m_ne(types.int.val(1, ctx=ctx), ctx=ctx),
    )
    bv = z3.BitVec(random_name('ord_bv'), 8)
    ctx.given.add(types.bool(z3.Unit(bv) == val.expr))
    return types.int(z3.BV2Int(bv))


@register('builtins.abs')
def builtins_abs(x: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    return x.m_abs(ctx=ctx)


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
def builtins_bool(obj: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    return obj.m_bool(ctx=ctx)


@register('builtins.set')
def builtins_set(iterable=None, **kwargs) -> ProxySort:
    if iterable is not None:
        if isinstance(iterable, types.set):
            return iterable
        raise UnsupportedError('unsupported argument for set()')
    return UntypedSetSort()


@register('builtins.list')
def builtins_list(iterable=None, **kwargs) -> ProxySort:
    if iterable is not None:
        if isinstance(iterable, types.list):
            return iterable
        raise UnsupportedError('unsupported argument for list()')
    return UntypedListSort()


@register('builtins.dict')
def builtins_dict(iterable=None, **kwargs) -> ProxySort:
    if iterable is not None:
        if isinstance(iterable, types.dict):
            return iterable
        raise UnsupportedError('unsupported argument for dict()')
    return UntypedDictSort()
