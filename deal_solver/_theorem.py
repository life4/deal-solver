import enum
import typing
from textwrap import dedent

import astroid
import z3

from ._annotations import ann2type
from ._cached_property import cached_property
from ._context import Context
from ._eval_contracts import Contract, eval_contracts
from ._eval_stmt import eval_stmt
from ._exceptions import ProveError, UnsupportedError
from ._model import Model
from ._proxies import BoolSort, and_expr


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
    example: typing.Optional[Model] = None

    @property
    def color(self) -> str:
        if self.conclusion == Conclusion.OK:
            return 'green'
        if self.conclusion == Conclusion.FAIL:
            return 'red'
        return 'yellow'

    def evolve(self, **kwargs) -> 'Proof':
        return self._replace(**kwargs)

    def __str__(self) -> str:
        msg = f'{self.description}'
        if self.error:
            msg += f' ({self.error})'
        if self.example:
            msg += f'. Example: {self.example}.'
        return msg


class Constraint(typing.NamedTuple):
    condition: BoolSort
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
                continue

            if isinstance(node, astroid.ClassDef):
                for subnode in node.body:
                    if not isinstance(subnode, astroid.FunctionDef):
                        continue
                    if not subnode.type == 'staticmethod':
                        continue
                    yield cls(node=subnode, timeout=timeout)

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
            sort = ann2type(name=arg.name, node=annotation, ctx=self._z3_context)
            if sort is None:
                raise UnsupportedError('unsupported annotation type', annotation.as_string())
            result[arg.name] = sort
        return result

    @property
    def constraints(self) -> typing.Iterator[Constraint]:
        eval_stmt(node=self._func, ctx=self._context)
        contracts = eval_contracts(func=self._func, ctx=self._context)

        given = and_expr(
            *contracts.pre,
            *self._context.given,
            ctx=self._context,
        )
        for exc in self._context.exceptions:
            if exc.names & contracts.raises:
                continue
            descr = exc.name
            if exc.message:
                descr += ': {}'.format(exc.message)
            yield Constraint(
                description=descr,
                condition=self._imply(
                    given=given,
                    expected=exc.cond,
                ),
            )
        for constraint in self._context.expected:
            yield Constraint(
                description='assertion',
                condition=self._imply(
                    given=given,
                    expected=constraint.m_not(ctx=self._context),
                ),
            )
        for constraint in contracts.post:
            yield Constraint(
                description='post-condition',
                condition=self._imply(
                    given=given,
                    expected=constraint.m_not(ctx=self._context),
                ),
            )

    def _imply(self, given: BoolSort, expected: BoolSort) -> BoolSort:
        expr = z3.And(
            given.expr,
            z3.Implies(given.expr, expected.expr, ctx=self._z3_context),
        )
        return BoolSort(expr=expr)

    def prove(self) -> Proof:
        try:
            self.arguments
        except UnsupportedError as exc:
            return Proof(
                conclusion=Conclusion.SKIP,
                description='failed to interpret function arguments',
                error=exc,
                example=None,
            )

        proofs = []
        for constraint in self.constraints:
            solver = z3.Solver(ctx=self._z3_context)
            solver.set('timeout', int(self._timeout * 1000))
            solver.add(constraint.condition.expr)
            proof = self._prove(solver=solver, descr=constraint.description)
            if proof.conclusion == Conclusion.FAIL:
                return proof
            proofs.append(proof)
        for skip in self._context.skips:
            proofs.append(Proof(
                conclusion=Conclusion.SKIP,
                description='failed to interpret statement',
                error=skip,
                example=None,
            ))
        return self._select_proof(proofs=proofs)

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
                example=Model(solver.model()),
            )
        raise RuntimeError('unreachable')

    @staticmethod
    def _select_proof(proofs: typing.List[Proof]) -> Proof:
        assert all(proof.conclusion != Conclusion.FAIL for proof in proofs)
        if not proofs:
            return Proof(
                conclusion=Conclusion.OK,
                description='nothing to prove',
            )
        some_ok = any(proof.conclusion == Conclusion.OK for proof in proofs)
        # if all proofs are skipped, just return the first one
        if not some_ok:
            return proofs[0]
        # if some proofs are skipped but some are ok, it is a partial proof
        for proof in proofs:
            if proof.conclusion == Conclusion.SKIP:
                return proof.evolve(conclusion=Conclusion.PARTIAL)
        # if all proofs are ok, all is good
        assert all(proof.conclusion == Conclusion.OK for proof in proofs)
        return Proof(
            conclusion=Conclusion.OK,
            description=', '.join(p.description for p in proofs),
            error=None,
            example=None,
        )
