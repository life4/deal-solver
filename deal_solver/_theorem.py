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
from ._eval_contracts import eval_contracts, Contracts
from ._eval_stmt import eval_stmt
from ._exceptions import ProveError, UnsupportedError
from ._proxies import wrap
from ._types import Z3Bool


class Conclusion(enum.Enum):
    OK = 'proved!'
    PARTIAL = 'partially proved'
    SKIP = 'skipped'
    FAIL = 'failed'

    @property
    def color(self) -> str:
        if self == Conclusion.OK:
            return 'green'
        if self == Conclusion.FAIL:
            return 'red'
        return 'yellow'


class TheoremResult(typing.NamedTuple):
    conclusion: Conclusion
    description: str
    error: typing.Optional[Exception] = None
    example: typing.Optional[z3.ModelRef] = None


class Constraint(typing.NamedTuple):
    condition: Z3Bool
    description: str


class Theorem:
    _func: astroid.FunctionDef
    result: typing.Optional[TheoremResult] = None

    def __init__(self, node: astroid.FunctionDef) -> None:
        self._func = node

    @classmethod
    def from_text(cls, content: str) -> typing.Iterator['Theorem']:
        content = dedent(content)
        module = cls._parse(content)
        yield from cls.from_astroid(module)

    @classmethod
    def from_astroid(cls, module: astroid.Module) -> typing.Iterator['Theorem']:
        for node in module.values():
            if isinstance(node, astroid.FunctionDef):
                yield cls(node=node)

    @property
    def name(self) -> str:
        return self._func.name or 'unknown_function'

    @property
    def conclusion(self) -> Conclusion:
        if self.result is None:
            msg = 'prove() must be called before accessing conclusion'
            raise RuntimeError(msg)
        return self.result.conclusion

    @cached_property
    def z3_context(self) -> typing.Optional[z3.Context]:
        # return z3.Context()
        return None

    @cached_property
    def context(self) -> Context:
        ctx = Context.make_empty()
        ctx = ctx.evolve(z3_ctx=self.z3_context)
        for name, value in self.arguments.items():
            ctx.scope.set(name=name, value=value)
        return ctx

    @cached_property
    def contracts(self) -> Contracts:
        return eval_contracts(
            decorators=self._func.decorators,
            ctx=self.context,
        )

    @cached_property
    def arguments(self) -> typing.Dict[str, z3.SortRef]:
        result = dict()
        args: astroid.Arguments = self._func.args
        for arg, annotation in zip(args.args, args.annotations):
            if annotation is None:
                raise UnsupportedError('missed annotation for', arg.name)
            sort = ann2sort(annotation, ctx=self.z3_context)
            if sort is None:
                raise UnsupportedError('unsupported annotation type', annotation.as_string())
            result[arg.name] = wrap(z3.Const(name=arg.name, sort=sort))
        return result

    @property
    def constraints(self) -> typing.Iterator[Constraint]:
        eval_stmt(node=self._func, ctx=self.context)

        for constraint in self.context.expected:
            yield Constraint(
                description='assertion',
                condition=z3.And(
                    *self.contracts.pre,
                    *self.context.given,
                    z3.Not(constraint),
                ),
            )
        for constraint in self.contracts.post:
            yield Constraint(
                description='post-condition',
                condition=z3.And(
                    *self.contracts.pre,
                    *self.context.given,
                    z3.Not(constraint),
                ),
            )
        for exc in self.context.exceptions:
            if exc.names & self.contracts.raises:
                continue
            yield Constraint(
                description=f'exception {exc.names}',
                condition=z3.And(
                    *self.contracts.pre,
                    *self.context.given,
                    exc.cond,
                ),
            )

    def reset(self) -> None:
        func = self._func
        self.__dict__.clear()
        self._func = func

    def prove(self) -> None:
        if self.result is not None:
            raise RuntimeError('already proved')
        self.result = TheoremResult(
            conclusion=Conclusion.OK,
            description='nothing to prove',
        )
        for constraint in self.constraints:
            solver = z3.Solver(ctx=self.z3_context)
            solver.add(constraint.condition)
            ok = self._prove(solver=solver, descr=constraint.description)
            if not ok:
                return

    def _prove(self, solver: z3.Solver, descr: str) -> bool:
        try:
            result = solver.check()
        except UnsupportedError as exc:
            self.result = TheoremResult(
                conclusion=Conclusion.SKIP,
                description=descr,
                error=exc,
                example=None,
            )
            return True

        if result == z3.unsat:
            self.result = TheoremResult(
                conclusion=Conclusion.OK,
                description=descr,
                error=None,
                example=None,
            )
            return True

        if result == z3.unknown:
            self.result = TheoremResult(
                conclusion=Conclusion.SKIP,
                description=descr,
                error=ProveError('cannot validate theorem'),
                example=None,
            )
            return True

        if result == z3.sat:
            self.result = TheoremResult(
                conclusion=Conclusion.FAIL,
                description=descr,
                error=None,
                example=solver.model(),
            )
            return False

        raise RuntimeError('unreachable')

    @staticmethod
    def _parse(text: str) -> astroid.Module:
        module = astroid.parse(text)
        return module
