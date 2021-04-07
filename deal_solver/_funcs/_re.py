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
