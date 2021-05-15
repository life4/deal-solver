import typing

import astroid

from ._proxy import ProxySort


if typing.TYPE_CHECKING:
    from .._context import Context


class LambdaSort(ProxySort):
    ctx: 'Context'
    args: astroid.Arguments
    body: astroid.Expr
    methods = ProxySort.methods.copy()

    def __init__(self, *, ctx: 'Context', args: astroid.Arguments, body) -> None:
        self.ctx = ctx
        self.args = args
        self.body = body

    @methods.add(name='__call__')
    def m_call(self, *values, **kwargs) -> ProxySort:
        from .._eval_expr import eval_expr

        body_ctx = self.ctx.make_child()
        for arg, value in zip(self.args.arguments, values):
            body_ctx.scope.set(name=arg.name, value=value)
        return eval_expr(node=self.body, ctx=body_ctx)
