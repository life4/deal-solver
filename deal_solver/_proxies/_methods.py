import typing


if typing.TYPE_CHECKING:
    from ._method import Method


F = typing.TypeVar('F', bound=typing.Callable)


class Methods:
    _registry: typing.Dict[str, 'Method']
    _raw: typing.List[dict]
    _final: bool

    def __init__(self) -> None:
        self._registry = dict()
        self._raw = []
        self._final = False

    def add(
        self, *,
        name: str,
        pure: bool = True,
        prop: bool = False,
    ) -> typing.Callable[[F], F]:
        def wrapper(f: F) -> F:
            assert not self._final
            self._raw.append(dict(
                name=name,
                impl=f,
                pure=pure,
                prop=prop,
            ))
            return f
        return wrapper

    def _finalize(self) -> None:
        from ._method import Method
        if self._final:
            return
        for raw in self._raw:
            self._registry[raw['name']] = Method(**raw)
        self._final = True
        self._raw = []

    def get(self, name: str) -> typing.Optional['Method']:
        self._finalize()
        return self._registry.get(name)

    def copy(self) -> 'Methods':
        new = type(self)()
        new._registry = self._registry.copy()
        new._raw = self._raw.copy()
        return new
