
# stdlib
import typing

# external
import z3

# app
from .._types import Z3Bool
from ._layer import Layer, ExceptionInfo, ReturnInfo
from ._scope import Scope
from ._trace import Trace


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
    given: Layer[Z3Bool]

    # Expected are checks we do validate. For example, all `assert` statements.
    expected: Layer[Z3Bool]

    exceptions: Layer[ExceptionInfo]    # all raised exceptions
    returns: Layer[ReturnInfo]          # all returned values

    # Trace is a collection of all function names in the current call stack.
    # It is used to mock recursive calls.
    trace: Trace

    @classmethod
    def make_empty(cls) -> 'Context':
        return cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
            given=Layer(),
            expected=Layer(),
            exceptions=Layer(),
            returns=Layer(),
            trace=Trace(),
        )

    @property
    def interrupted(self) -> Z3Bool:
        false = z3.BoolVal(False, ctx=self.z3_ctx)
        return z3.Or(
            false,
            *[exc.cond for exc in self.exceptions],
            *[ret.cond for ret in self.returns],
        )

    @property
    def return_value(self):
        returns = list(self.returns)
        if not returns:
            return None
        result = returns[0]
        for other in returns[1:]:
            result = result.merge(other)
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