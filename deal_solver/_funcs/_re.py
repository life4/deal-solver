# app
from .._context import Context
from .._proxies import BoolSort, ProxySort, PatternSort
from ._registry import register


@register('re.fullmatch')
def re_fullmatch(
    pattern: ProxySort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    pat_str = pattern.expr.as_string()
    pat = PatternSort.from_str(pat_str, flags=0)
    return pat.fullmatch(string, ctx=ctx)


@register('re.match')
def re_match(
    pattern: ProxySort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    pat_str = pattern.expr.as_string()
    pat = PatternSort.from_str(pat_str, flags=0)
    return pat.match(string, ctx=ctx)


@register('re.compile')
def re_compile(
    pattern: ProxySort,
    **kwargs,
) -> PatternSort:
    pat_str = pattern.expr.as_string()
    return PatternSort.from_str(pat_str, flags=0)


@register('re.Pattern.fullmatch')
def re_pattern_fullmatch(
    pattern: PatternSort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    return pattern.fullmatch(string, ctx=ctx)


@register('re.Pattern.match')
def re_pattern_match(
    pattern: PatternSort,
    string: ProxySort,
    ctx: Context,
    **kwargs,
) -> BoolSort:
    return pattern.match(string, ctx=ctx)