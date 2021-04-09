import typing


if typing.TYPE_CHECKING:
    from ._method import Method


F = typing.TypeVar('F', bound=typing.Callable)


class Methods:
    _registry: typing.Dict[str, 'Method']

    def __init__(self) -> None:
        self._registry = dict()

    def add(self, *, name: str, pure: bool = True) -> typing.Callable[[F], F]:
        from ._method import Method
        assert name not in self._registry

        def wrapper(f: F) -> F:
            self._registry[name] = Method(
                name=name,
                impl=f,
                pure=pure,
            )
            return f
        return wrapper

    def get(self, name: str) -> typing.Optional['Method']:
        return self._registry.get(name)

    def copy(self) -> 'Methods':
        new = type(self)()
        new._registry = self._registry.copy()
        return new
