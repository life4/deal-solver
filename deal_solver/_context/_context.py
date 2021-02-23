
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
    z3_ctx: typing.Optional[z3.Context]
    scope: Scope
    given: Layer[Z3Bool]
    expected: Layer[Z3Bool]
    exceptions: Layer[ExceptionInfo]
    returns: Layer[ReturnInfo]
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
            *[ret.cond for ret in self.returns]
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
