# stdlib
import typing

# external
import z3


if typing.TYPE_CHECKING:
    # app
    from .._proxies import BoolSort


T = typing.TypeVar('T')


class ExceptionInfo(typing.NamedTuple):
    name: str               # exception name
    names: typing.Set[str]  # exception name and names of all its bases
    cond: 'BoolSort'        # indicates if the exception is raised
    message: str = ''


class ReturnInfo(typing.NamedTuple):
    value: typing.Any
    cond: 'BoolSort'

    def merge(self, other: 'ReturnInfo') -> 'ReturnInfo':
        # app
        from .._proxies import if_expr

        true = z3.BoolVal(True)
        cls = type(self)
        return cls(
            cond=if_expr(self.cond, true, other.cond),
            value=if_expr(self.cond, self.value, other.value),
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
