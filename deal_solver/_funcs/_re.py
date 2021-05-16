from .._context import Context
from .._proxies import BoolSort, PatternSort, ProxySort
from ._registry import register


@register('re.fullmatch')
def re_fullmatch(
    pattern: ProxySort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    pat_str = pattern.expr.as_string()
    pat = PatternSort.val(pat_str)
    return pat.fullmatch(string, ctx=ctx)


@register('re.match')
def re_match(
    pattern: ProxySort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    pat_str = pattern.expr.as_string()
    pat = PatternSort.val(pat_str)
    return pat.match(string, ctx=ctx)


@register('re.compile')
def re_compile(
    pattern: ProxySort,
    **kwargs,
) -> PatternSort:
    pat_str = pattern.expr.as_string()
    return PatternSort.val(pat_str)
