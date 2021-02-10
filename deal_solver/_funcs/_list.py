# app
from .._context import Context
from .._exceptions import UnsupportedError
from .._proxies import IntSort, ListSort
from ._registry import register


@register('builtins.list.index')
def list_index(items: ListSort, item, start=None, **kwargs):
    return items.index(item, start=start)


@register('builtins.list.append')
def list_append(items: ListSort, item, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        raise UnsupportedError(f'cannot append to {var_name}')
    ctx.scope.set(
        name=var_name,
        value=items.append(item),
    )


@register('builtins.list.extend')
def list_extend(items: ListSort, other, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        raise UnsupportedError(f'cannot extend {var_name}')
    ctx.scope.set(
        name=var_name,
        value=items + other,
    )


@register('builtins.list.count')
def list_count(items: ListSort, item, **kwargs) -> IntSort:
    return items.count(item)
