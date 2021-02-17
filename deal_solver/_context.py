# stdlib
import typing
from collections import Counter
from contextlib import contextmanager

# external
import z3

# app
from ._types import SortType, Z3Bool


class Asserts:
    layer: typing.List[Z3Bool]
    _parent: typing.Optional['Asserts']

    def __init__(self, parent=None) -> None:
        self.layer = []
        self._parent = parent

    def add(self, cond: Z3Bool) -> None:
        self.layer.append(cond)

    def make_child(self) -> 'Asserts':
        cls = type(self)
        return cls(parent=self)

    def __iter__(self) -> typing.Iterator[Z3Bool]:
        yield from self.layer
        if self._parent:
            yield from self._parent

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )


class ExceptionInfo(typing.NamedTuple):
    names: typing.Set[str]
    cond: Z3Bool


class Exceptions:
    _parent: typing.Optional['Exceptions']
    layer: typing.List[ExceptionInfo]

    def __init__(self, parent: typing.Optional['Exceptions'] = None) -> None:
        self._parent = parent
        self.layer = []

    def make_child(self) -> 'Exceptions':
        cls = type(self)
        return cls(parent=self)

    def add(self, *, names: typing.Set[str], cond: Z3Bool) -> None:
        self.layer.append(ExceptionInfo(names=names, cond=cond))

    def __iter__(self) -> typing.Iterator[ExceptionInfo]:
        yield from self.layer
        if self._parent:
            yield from self._parent

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )


class Scope:
    _parent: typing.Optional['Scope']
    layer: typing.Dict[str, SortType]

    def __init__(self, parent: typing.Optional['Scope'], vars) -> None:
        self._parent = parent
        self.layer = vars

    @classmethod
    def make_empty(cls) -> 'Scope':
        return cls(
            vars=dict(),
            parent=None,
        )

    def make_child(self) -> 'Scope':
        cls = type(self)
        return cls(
            parent=self,
            vars=dict(),
        )

    def get(self, name: str) -> typing.Optional[SortType]:
        var = self.layer.get(name)
        if var is not None:
            return var
        if self._parent is not None:
            return self._parent.get(name=name)
        return None

    def set(self, name: str, value: SortType) -> None:
        self.layer[name] = value

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )


class Trace:
    __slots__ = ['_names']
    _names: Counter

    def __init__(self) -> None:
        self._names = Counter()

    @contextmanager
    def guard(self, name: str) -> typing.Iterator[None]:
        self._names[name] += 1
        try:
            yield
        finally:
            self._names[name] -= 1

    def __contains__(self, name: str) -> bool:
        return self._names[name] > 0

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=', '.join(sorted(self._names)),
        )


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
    def evolve(self) -> typing.Callable[..., 'Context']:
        return self._replace

    def make_child(self) -> 'Context':
        return self.evolve(
            scope=self.scope.make_child(),
            given=self.given.make_child(),
            expected=self.expected.make_child(),
            exceptions=self.exceptions.make_child(),
        )
