from __future__ import annotations

import typing


if typing.TYPE_CHECKING:
    from .._proxies import ProxySort


class Scope:
    __slots__ = ['layer', 'parent']

    layer: dict[str, ProxySort]
    parent: Scope | None

    def __init__(self, parent: Scope | None, vars) -> None:
        self.parent = parent
        self.layer = vars

    @classmethod
    def make_empty(cls) -> Scope:
        return cls(
            vars=dict(),
            parent=None,
        )

    def make_child(self) -> Scope:
        cls = type(self)
        return cls(
            parent=self,
            vars=dict(),
        )

    def get(self, name: str) -> ProxySort | None:
        var = self.layer.get(name)
        if var is not None:
            return var
        if self.parent is not None:
            return self.parent.get(name=name)
        return None

    def set(self, name: str, value: ProxySort) -> None:
        self.layer[name] = value
