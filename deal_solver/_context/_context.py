
# stdlib
import typing

# external
import z3

# app
from .._types import Z3Bool
from ._asserts import Asserts
from ._exceptions import Exceptions
from ._scope import Scope
from ._trace import Trace


class Context(typing.NamedTuple):
    z3_ctx: typing.Optional[z3.Context]
    scope: Scope
    given: Asserts
    expected: Asserts
    exceptions: Exceptions
    trace: Trace

    @classmethod
    def make_empty(cls) -> 'Context':
        return cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
            given=Asserts(),
            expected=Asserts(),
            exceptions=Exceptions(),
            trace=Trace(),
        )

    @property
    def interrupted(self) -> Z3Bool:
        if self.exceptions.empty:
            return z3.BoolVal(False, ctx=self.z3_ctx)
        constr = [exc.cond for exc in self.exceptions]
        return z3.Or(*constr)

    @property
    def evolve(self) -> typing.Callable[..., 'Context']:
        return self._replace

    def make_child(self) -> 'Context':
        return self.evolve(
            scope=self.scope.make_child(),
            given=self.given.make_child(),
            expected=self.expected.make_child(),
            exceptions=self.exceptions.make_child(),
        )
