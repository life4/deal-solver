import z3

from .._context import Context
from .._proxies import ProxySort, StrSort
from ._registry import register


@register('posixpath.join')
@register('ntpath.join')
@register('os.path.join')
def os_path_join(first_arg: ProxySort, *args: ProxySort, ctx: Context, **kwargs) -> ProxySort:
    sep = StrSort(z3.StringVal('/'))

    if not isinstance(first_arg, StrSort):
        msg = 'expected str, bytes or os.PathLike object, not {}'
        msg = msg .format(first_arg.type_name)
        ctx.add_exception(TypeError, msg)
        return sep

    for arg in args:
        if not isinstance(arg, StrSort):
            msg = 'expected str, bytes or os.PathLike object, not int'
            msg = msg .format(arg.type_name)
            ctx.add_exception(TypeError, msg)
            return sep
        first_arg = first_arg.m_add(sep, ctx=ctx).m_add(arg, ctx=ctx)
    return first_arg
