# stdlib
import typing

# app
from .._types import Z3Bool


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

    @property
    def empty(self) -> bool:
        if self.layer:
            return False
        if self._parent:
            return self._parent.empty
        return True

    def __iter__(self) -> typing.Iterator[ExceptionInfo]:
        yield from self.layer
        if self._parent:
            yield from self._parent

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )
