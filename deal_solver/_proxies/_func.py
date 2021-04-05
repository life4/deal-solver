# stdlib
import typing

# app
from ._proxy import ProxySort
from ._registry import registry


if typing.TYPE_CHECKING:
    # app
    from .._context import Context


F = typing.Callable[..., ProxySort]


@registry.add
class FuncSort(ProxySort):
    type_name = 'function'
    impl: F

    def __init__(self, impl: F) -> None:
        self.impl = impl  # type: ignore

    def m_call(self, *args, ctx: 'Context', var_name: str, **kwargs) -> 'ProxySort':
        """self(*args, **kwargs)
        """
        return self.impl(*args, ctx=ctx, var_name=var_name, **kwargs)
