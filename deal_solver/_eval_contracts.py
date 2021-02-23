# stdlib
import typing

# external
import astroid
import z3

# app
from ._context import Context, Scope
from ._eval_expr import eval_expr
from ._goal import Goal
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
                if value is None:
                    continue
                goals.post.add(value)
        if contract.name == 'raises':
            values = _eval_raises(ctx=ctx, args=contract.args)
            goals.raises.update(values)
    return goals


def _eval_pre(ctx: Context, args: list):
    contract = args[0]
    if not isinstance(contract, astroid.Lambda):
        return
    if not contract.args:
        return
    return eval_expr(node=contract.body, ctx=ctx)


def _eval_post(ctx: Context, args: list):
    contract = args[0]
    if not isinstance(contract, astroid.Lambda):
        return
    if not contract.args:
        return
    cargs = contract.args.arguments
    for ret in ctx.returns:
        ctx = ctx.evolve(scope=Scope.make_empty())
        ctx.scope.set(
            name=cargs[0].name,
            value=ret.value,
        )
        # The contract is valid if the return value is not reached
        # or it passed the pos-condition test.
        yield z3.Or(
            z3.Not(ret.cond),
            eval_expr(node=contract.body, ctx=ctx),
        )


def _eval_raises(ctx: Context, args: list):
    for arg in args:
        if isinstance(arg, astroid.Name):
            yield arg.name
