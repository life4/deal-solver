# stdlib
import typing

# app
from .._types import Z3Bool


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
