# stdlib
import typing

# external
import astroid

# app
from ._ast import get_name
from ._context import Context, Scope
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError
from ._goal import Goal


SUPPORTED_CONTRACTS = {'deal.pre', 'deal.post', 'deal.raises', 'deal.pure', 'deal.has'}
SUPPORTED_MARKERS = {'deal.pure'}


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


def eval_contracts(decorators: astroid.Decorators, ctx: Context) -> typing.Dict[str, Goal]:
    goals = dict(
        pre=Goal(),
        post=Goal(),
    )
    if not decorators:
        return goals
    return_value = ctx.scope.get('return')
    for contract_name, args in get_contracts(decorators.nodes):
        if contract_name not in {'pre', 'post'}:
            continue
        if contract_name == 'post' and return_value is None:
            raise UnsupportedError('cannot resolve return value to check deal.post')
        contract = args[0]
        if not isinstance(contract, astroid.Lambda):
            continue
        if not contract.args:
            continue

        # make context
        cargs = contract.args.arguments
        contract_context = ctx
        if contract_name == 'post':
            assert return_value is not None
            # check post-condition in a new clear scope
            # with mapping `return` value in it as an argument.
            contract_context = contract_context.evolve(scope=Scope.make_empty())
            contract_context.scope.set(
                name=cargs[0].name,
                value=return_value,
            )

        # eval contract
        value = eval_expr(node=contract.body, ctx=contract_context)
        goals[contract_name].add(value)
    return goals
