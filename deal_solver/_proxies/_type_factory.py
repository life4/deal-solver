import typing


if typing.TYPE_CHECKING:
    from ._proxy import ProxySort


class TypeFactory(typing.NamedTuple):
    type: typing.Type['ProxySort']
    default: 'ProxySort'
    subtypes: typing.Tuple[object, ...]

    @property
    def type_name(self) -> str:
        return self.type.type_name

    @property
    def sort(self):
        return self.default.sort()

    def wrap(self, expr) -> 'ProxySort':
        if self.subtypes:
            return self.type(expr, subtypes=self.subtypes)  # type: ignore
        return self.type(expr)

    def match(self, factory: 'TypeFactory') -> bool:
        if not issubclass(factory.type, self.type):
            return False
        for t1, t2 in zip(self.subtypes, factory.subtypes):
            assert isinstance(t1, TypeFactory)
            assert isinstance(t2, TypeFactory)
            if not t1.match(t2):
                return False
        return True
