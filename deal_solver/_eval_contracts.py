# stdlib
import typing

# external
import astroid
import z3

# app
from ._ast import get_name
from ._context import Context, Scope
from ._eval_expr import eval_expr
from ._goal import Goal


SUPPORTED_CONTRACTS = {'deal.pre', 'deal.post', 'deal.raises'}
SUPPORTED_MARKERS = {'deal.pure'}


class Contracts(typing.NamedTuple):
    pre: Goal
    post: Goal
    raises: typing.Set[str]


def get_contracts(decorators: typing.List) -> typing.Iterator[typing.Tuple[str, list]]:
    for contract in decorators:
        if isinstance(contract, astroid.Attribute):
            name = get_name(contract)
            if name not in SUPPORTED_MARKERS:
                continue
            yield name.split('.')[-1], []

        if isinstance(contract, astroid.Call):
            if not isinstance(contract.func, astroid.Attribute):
                continue
            name = get_name(contract.func)
            if name == 'deal.chain':
                yield from get_contracts(contract.args)
            if name not in SUPPORTED_CONTRACTS:
                continue
            yield name.split('.')[-1], contract.args

        # infer assigned value
        if isinstance(contract, astroid.Name):
            assigments = contract.lookup(contract.name)[1]
            if not assigments:
                continue
            # use only the closest assignment
            expr = assigments[0]
            # can it be not an assignment? IDK
            if not isinstance(expr, astroid.AssignName):  # pragma: no cover
                continue
            expr = expr.parent
            if not isinstance(expr, astroid.Assign):  # pragma: no cover
                continue
            yield from get_contracts([expr.value])


def eval_contracts(decorators: astroid.Decorators, ctx: Context) -> Contracts:
    goals = Contracts(
        pre=Goal(),
        post=Goal(),
        raises=set(),
    )
    if not decorators:
        return goals
    for contract_name, args in get_contracts(decorators.nodes):
        if contract_name == 'pre':
            value = _eval_pre(ctx=ctx, args=args)
            if value is None:
                continue
            goals.pre.add(value)
        if contract_name == 'post':
            for value in _eval_post(ctx=ctx, args=args):
                if value is None:
                    continue
                goals.post.add(value)
        if contract_name == 'raises':
            values = _eval_raises(ctx=ctx, args=args)
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
