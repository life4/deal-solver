import typing

from ._proxy import ProxySort
from .._exceptions import UnsupportedError

if typing.TYPE_CHECKING:
    from .._context import Context


class Method(ProxySort):
    type_name = 'method'

    name: str
    impl: typing.Callable
    pure: bool
    obj: typing.Optional[ProxySort]

    def __init__(self, name, impl, pure, obj=None) -> None:
        self.name = name
        self.impl = impl  # type: ignore
        self.pure = pure
        self.obj = obj

    def with_obj(self, obj: ProxySort) -> 'Method':
        return type(self)(
            name=self.name,
            impl=self.impl,
            pure=self.pure,
            obj=obj,
        )

    def m_call(self, *args, ctx: 'Context', var_name: str, **kwargs) -> ProxySort:
        assert self.obj is not None
        result = self.impl(self.obj, *args, ctx=ctx, **kwargs)
        if not self.pure:
            if not var_name.isidentifier():
                raise UnsupportedError('cannot modify attribute', var_name)
            ctx.scope.set(name=var_name, value=result)
        return result
