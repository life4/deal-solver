# stdlib
import typing

# external
import astroid

# app
from ._proxy import ProxySort


if typing.TYPE_CHECKING:
    # app
    from .._context import Context


class LambdaSort(ProxySort):
    ctx: 'Context'
    args: astroid.Arguments
    body: astroid.Expr

    def __init__(self, *, ctx: 'Context', args: astroid.Arguments, body) -> None:
        self.ctx = ctx
        self.args = args
        self.body = body

    def m_call(self, *values, **kwargs) -> ProxySort:
        # app
        from .._eval_expr import eval_expr

        body_ctx = self.ctx.make_child()
        for arg, value in zip(self.args.arguments, values):
            body_ctx.scope.set(name=arg.name, value=value)
        return eval_expr(node=self.body, ctx=body_ctx)
