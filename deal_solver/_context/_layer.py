# stdlib
import typing

import z3

# app
from .._types import Z3Bool


T = typing.TypeVar('T')


class ExceptionInfo(typing.NamedTuple):
    names: typing.Set[str]  # exception name and names of all its bases
    cond: Z3Bool            # indicates if the exception is raised


class ReturnInfo(typing.NamedTuple):
    value: typing.Any
    cond: Z3Bool

    def merge(self, other: 'ReturnInfo') -> 'ReturnInfo':
        cls = type(self)
        return cls(
            cond=z3.Or(self.cond, other.cond),
            value=z3.If(self.cond, self.value, other.value),
        )


class Layer(typing.Generic[T]):
    __slots__ = ['layer', 'parent']

    layer: typing.List[T]
    parent: typing.Optional['Layer[T]']

    def __init__(self, parent=None) -> None:
        self.layer = []
        self.parent = parent

    def add(self, item: T) -> None:
        self.layer.append(item)

    def make_child(self) -> 'Layer[T]':
        cls = type(self)
        return cls(parent=self)

    def __iter__(self) -> typing.Iterator[T]:
        yield from self.layer
        if self.parent:
            yield from self.parent

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )
