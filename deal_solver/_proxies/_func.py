import typing

import astroid

from .._exceptions import UnsupportedError
from ._funcs import and_expr
from ._proxy import ProxySort
from ._registry import types


if typing.TYPE_CHECKING:
    from .._context import Context


F = typing.Callable[..., ProxySort]


@types.add
class FuncSort(ProxySort):
    type_name = 'function'
    impl: F
    methods = ProxySort.methods.copy()

    def __init__(self, impl: F) -> None:
        self.impl = impl  # type: ignore

    @methods.add(name='__call__')
    def m_call(self, *args: ProxySort, ctx: 'Context', var_name=None, **kwargs: ProxySort) -> ProxySort:
        """self(*args, **kwargs)
        """
        if isinstance(self.impl, astroid.FunctionDef):
            return self._call_function(
                node=self.impl,
                ctx=ctx,
                call_args=args,
                call_kwargs=kwargs,
            )
        return self.impl(*args, ctx=ctx, **kwargs)

    @staticmethod
    def _call_function(
        node: astroid.FunctionDef,
        ctx: 'Context',
        call_args: typing.Tuple[ProxySort, ...],
        call_kwargs: typing.Dict[str, ProxySort],
    ) -> ProxySort:
        from .._eval_contracts import eval_contracts
        from .._eval_stmt import eval_stmt

        # put arguments into the scope
        func_ctx = ctx.make_empty(get_contracts=ctx.get_contracts, trace=ctx.trace)
        for arg, value in zip(node.args.args or [], call_args):
            func_ctx.scope.set(name=arg.name, value=value)
        for name, value in call_kwargs.items():
            func_ctx.scope.set(name=name, value=value)

        # call the function
        eval_stmt(node=node, ctx=func_ctx)
        result = func_ctx.return_value
        if result is None:
            raise UnsupportedError('cannot find return value for', node.name)

        # we ask pre-conditions to be true
        # and promise post-condition to be true
        contracts = eval_contracts(func=node, ctx=func_ctx)
        ctx.expected.add(and_expr(*contracts.pre, ctx=ctx))
        ctx.given.add(and_expr(*contracts.post, ctx=ctx))

        return result
