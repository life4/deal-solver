import typing

from .._exceptions import UnsupportedError
from ._proxy import ProxySort


if typing.TYPE_CHECKING:
    from .._context import Context


class Mutation(typing.NamedTuple):
    new_value: ProxySort
    result: ProxySort


class Method(ProxySort):
    type_name = 'method'
    methods = ProxySort.methods.copy()

    name: str
    impl: typing.Callable
    pure: bool
    prop: bool
    obj: typing.Optional[ProxySort]

    def __init__(self, name, impl, pure, prop, obj=None) -> None:
        self.name = name
        self.impl = impl  # type: ignore
        self.pure = pure
        self.prop = prop
        self.obj = obj

    def with_obj(self, obj: ProxySort) -> 'Method':
        return type(self)(
            name=self.name,
            impl=self.impl,
            pure=self.pure,
            prop=self.prop,
            obj=obj,
        )

    @methods.add(name='__call__')
    def m_call(self, *args, ctx: 'Context', var_name: str = '', **kwargs) -> ProxySort:
        assert self.obj is not None
        result = self.impl(self.obj, *args, ctx=ctx, **kwargs)
        if isinstance(result, Mutation):
            assert not self.pure
            new_value = result.new_value
            result = result.result
        else:
            new_value = result
        if not self.pure and var_name:
            if not var_name.isidentifier():
                raise UnsupportedError('cannot modify', var_name)
            ctx.scope.set(name=var_name, value=new_value)
        return result
