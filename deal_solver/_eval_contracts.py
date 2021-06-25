import typing

import astroid

from ._context import Context, Scope
from ._eval_expr import eval_expr
from ._goal import Goal
from ._proxies import BoolSort, or_expr
from ._types import AstNode


class Contract(typing.NamedTuple):
    """
    + `name` can be `pre`, `post`, or `raises`. Everything else is ignored.
    + `args` contains one node for `pre` and `post` (which is the validator)
      and many nodes for `raises` (which are exceptions).
    """
    name: str
    args: typing.List[AstNode]


class Contracts(typing.NamedTuple):
    pre: Goal
    post: Goal
    raises: typing.Set[str]


def eval_contracts(func: astroid.FunctionDef, ctx: Context) -> Contracts:
    goals = Contracts(
        pre=Goal(),
        post=Goal(),
        raises=set(),
    )
    for contract in ctx.get_contracts(func):
        if contract.name == 'pre':
            value = _eval_pre(ctx=ctx, args=contract.args)
            if value is None:
                continue
            goals.pre.add(value)
        if contract.name == 'post':
            for value in _eval_post(ctx=ctx, args=contract.args):
                goals.post.add(value)
        if contract.name == 'ensure':
            for value in _eval_ensure(ctx=ctx, args=contract.args):
                goals.post.add(value)
        if contract.name == 'raises':
            values = _eval_raises(ctx=ctx, args=contract.args)
            goals.raises.update(values)
    return goals


def _eval_pre(ctx: Context, args: list) -> typing.Optional[BoolSort]:
    contract = args[0]
    if not isinstance(contract, astroid.Lambda):
        return None
    assert contract.args
    ctx = ctx.make_child()
    return eval_expr(node=contract.body, ctx=ctx).m_bool(ctx=ctx)


def _eval_post(ctx: Context, args: list) -> typing.Iterator[BoolSort]:
    contract = args[0]
    if not isinstance(contract, astroid.Lambda):
        return
    assert contract.args
    cargs = contract.args.arguments
    ctx = ctx.evolve(scope=Scope.make_empty())
    for ret in ctx.returns:
        ctx.scope.set(
            name=cargs[0].name,
            value=ret.value,
        )
        # The contract is valid if the return value is not reached
        # or it passed the post-condition test.
        yield or_expr(
            ret.cond.m_not(ctx=ctx),
            eval_expr(node=contract.body, ctx=ctx),
            ctx=ctx,
        )


def _eval_ensure(ctx: Context, args: list) -> typing.Iterator[BoolSort]:
    contract = args[0]
    if not isinstance(contract, astroid.Lambda):
        return
    assert contract.args
    ctx = ctx.make_child()
    for ret in ctx.returns:
        ctx.scope.set(
            name='result',
            value=ret.value,
        )
        yield or_expr(
            ret.cond.m_not(ctx=ctx),
            eval_expr(node=contract.body, ctx=ctx),
            ctx=ctx,
        )


def _eval_raises(ctx: Context, args: list) -> typing.Iterator[str]:
    for arg in args:
        if isinstance(arg, astroid.Name):
            yield arg.name
