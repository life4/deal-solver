
import typing

import z3

from ._layer import ExceptionInfo, Layer, ReturnInfo
from ._scope import Scope
from ._trace import Trace


if typing.TYPE_CHECKING:
    from .._proxies import BoolSort, ProxySort


class Context(typing.NamedTuple):
    # z3 context which should be used everywhere where z3 asks to use it.
    # Since z3 freaks out when we provide an explicit context
    # (supposedly, because we forget to pass it in some places),
    # this value is always None at the moment.
    z3_ctx: typing.Optional[z3.Context]

    # Scope holds z3 values for all variables executed up to the current line.
    scope: Scope

    # Given are checks that we don't validate but assume them to be always true.
    # For example, post-conditions of all functions the current function calls.
    given: Layer['BoolSort']

    # Expected are checks we do validate. For example, all `assert` statements.
    expected: Layer['BoolSort']

    exceptions: Layer[ExceptionInfo]    # all raised exceptions
    returns: Layer[ReturnInfo]          # all returned values

    # Trace is a collection of all function names in the current call stack.
    # It is used to mock recursive calls.
    trace: Trace

    # exceptions occured during evaluation
    skips: typing.List[Exception]

    # the user-provided function to extract contracts from called functions
    get_contracts: typing.Callable[[typing.Any], typing.Iterator]

    @classmethod
    def make_empty(cls, *, get_contracts, **kwargs) -> 'Context':
        obj = cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
            given=Layer(),
            expected=Layer(),
            exceptions=Layer(),
            returns=Layer(),
            trace=Trace(),
            skips=[],
            get_contracts=get_contracts,
        )
        return obj.evolve(**kwargs)

    @property
    def interrupted(self) -> 'BoolSort':
        from .._proxies import or_expr
        return or_expr(
            *[exc.cond.m_bool(ctx=self) for exc in self.exceptions],
            *[ret.cond.m_bool(ctx=self) for ret in self.returns],
            ctx=self,
        )

    def add_exception(self, exc: type, msg: str = '', cond: 'BoolSort' = None) -> None:
        if cond is None:
            from .._proxies import BoolSort
            cond = BoolSort.val(True, ctx=self)

        self.exceptions.add(ExceptionInfo(
            name=exc.__name__,
            names={base.__name__ for base in exc.mro()[:-1]},
            cond=cond,
            message=msg,
        ))

    @property
    def return_value(self) -> typing.Optional['ProxySort']:
        returns = list(self.returns)
        if not returns:
            return None
        result = returns[0]
        for other in returns[1:]:
            result = result.merge(other, ctx=self)
        return result.value

    @property
    def evolve(self) -> typing.Callable[..., 'Context']:
        return self._replace

    def make_child(self) -> 'Context':
        return self.evolve(
            scope=self.scope.make_child(),
            given=self.given.make_child(),
            expected=self.expected.make_child(),
            exceptions=self.exceptions.make_child(),
            returns=self.returns.make_child(),
        )
