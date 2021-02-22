# stdlib
import typing

# app
from .._types import SortType


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
