import typing


if typing.TYPE_CHECKING:
    from ._proxy import ProxySort


class TypeInfo(typing.NamedTuple):
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
