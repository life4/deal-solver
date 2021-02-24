# stdlib
import enum
import typing
from textwrap import dedent

# external
import astroid
import z3

# app
from ._annotations import ann2sort
from ._cached_property import cached_property
from ._context import Context
from ._eval_contracts import Contract, eval_contracts
from ._eval_stmt import eval_stmt
from ._exceptions import ProveError, UnsupportedError
from ._proxies import wrap
from ._types import Z3Bool


DEFAULT_TIMEOUT = 5.0


class Conclusion(enum.Enum):
    OK = 'proved!'
    PARTIAL = 'partially proved'
    SKIP = 'skipped'
    FAIL = 'failed'


class Proof(typing.NamedTuple):
    conclusion: Conclusion
    description: str
    error: typing.Optional[Exception] = None
    example: typing.Optional[z3.ModelRef] = None

    @property
    def color(self) -> str:
        if self.conclusion == Conclusion.OK:
            return 'green'
        if self.conclusion == Conclusion.FAIL:
            return 'red'
        return 'yellow'


class Constraint(typing.NamedTuple):
    condition: Z3Bool
    description: str


class Theorem:
    _func: astroid.FunctionDef

    def __init__(
        self, *,
        node: astroid.FunctionDef,
        timeout: float = DEFAULT_TIMEOUT,
    ) -> None:
        self._func = node
        self._timeout = timeout

    @staticmethod
    def get_contracts(func: astroid.FunctionDef) -> typing.Iterator[Contract]:
        """The function should yield the information about contracts.

        Redefine this function for your needs.
        See tests/helpers.py for an example.
        """
        raise NotImplementedError

    @classmethod
    def from_text(
        cls,
        content: str, *,
        timeout: float = DEFAULT_TIMEOUT,
    ) -> typing.Iterator['Theorem']:
        content = dedent(content)
        module = astroid.parse(content)
        yield from cls.from_astroid(module=module, timeout=timeout)

    @classmethod
    def from_astroid(
        cls, *,
        module: astroid.Module,
        timeout: float = DEFAULT_TIMEOUT,
    ) -> typing.Iterator['Theorem']:
        for node in module.values():
            if isinstance(node, astroid.FunctionDef):
                yield cls(node=node, timeout=timeout)

    @property
    def name(self) -> str:
        return self._func.name or 'unknown_function'

    @cached_property
    def _z3_context(self) -> typing.Optional[z3.Context]:
        # return z3.Context()
        return None

    @cached_property
    def _context(self) -> Context:
        ctx = Context.make_empty(get_contracts=self.get_contracts)
        ctx = ctx.evolve(z3_ctx=self._z3_context)
        for name, value in self.arguments.items():
            ctx.scope.set(name=name, value=value)
        return ctx

    @cached_property
    def arguments(self) -> typing.Dict[str, z3.SortRef]:
        result = dict()
        args: astroid.Arguments = self._func.args
        for arg, annotation in zip(args.args, args.annotations):
            if annotation is None:
                raise UnsupportedError('missed annotation for', arg.name)
            sort = ann2sort(annotation, ctx=self._z3_context)
            if sort is None:
                raise UnsupportedError('unsupported annotation type', annotation.as_string())
            result[arg.name] = wrap(z3.Const(name=arg.name, sort=sort))
        return result

    @property
    def constraints(self) -> typing.Iterator[Constraint]:
        eval_stmt(node=self._func, ctx=self._context)
        contracts = eval_contracts(func=self._func, ctx=self._context)

        for constraint in self._context.expected:
            yield Constraint(
                description='assertion',
                condition=z3.And(
                    *contracts.pre,
                    *self._context.given,
                    z3.Not(constraint),
                ),
            )
        for constraint in contracts.post:
            yield Constraint(
                description='post-condition',
                condition=z3.And(
                    *contracts.pre,
                    *self._context.given,
                    z3.Not(constraint),
                ),
            )
        for exc in self._context.exceptions:
            if exc.names & contracts.raises:
                continue
            yield Constraint(
                description=f'exception {exc.names}',
                condition=z3.And(
                    *contracts.pre,
                    *self._context.given,
                    exc.cond,
                ),
            )

    def reset(self) -> None:
        func = self._func
        self.__dict__.clear()
        self._func = func

    def prove(self) -> Proof:
        result = Proof(
            conclusion=Conclusion.OK,
            description='nothing to prove',
        )
        for constraint in self.constraints:
            solver = z3.Solver(ctx=self._z3_context)
            solver.set('timeout', int(self._timeout * 1000))
            solver.add(constraint.condition)
            result = self._prove(solver=solver, descr=constraint.description)
            if result.conclusion == Conclusion.FAIL:
                return result
        return result

    @staticmethod
    def _prove(solver: z3.Solver, descr: str) -> Proof:
        result = solver.check()

        if result == z3.unsat:
            return Proof(
                conclusion=Conclusion.OK,
                description=descr,
                error=None,
                example=None,
            )

        if result == z3.unknown:
            return Proof(
                conclusion=Conclusion.SKIP,
                description=descr,
                error=ProveError(solver.reason_unknown()),
                example=None,
            )

        if result == z3.sat:
            return Proof(
                conclusion=Conclusion.FAIL,
                description=descr,
                error=None,
                example=solver.model(),
            )

        raise RuntimeError('unreachable')
