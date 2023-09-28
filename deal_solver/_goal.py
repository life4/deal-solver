from __future__ import annotations

from typing import Iterator

from ._proxies import BoolSort


class Goal:
    _items: list[BoolSort]

    def __init__(self) -> None:
        self._items = []

    def add(self, item: BoolSort) -> None:
        self._items.append(item)

    def __iter__(self) -> Iterator[BoolSort]:
        yield from self._items
