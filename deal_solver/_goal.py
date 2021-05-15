from typing import Iterator, List

from ._proxies import BoolSort


class Goal:
    _items: List[BoolSort]

    def __init__(self) -> None:
        self._items = []

    def add(self, item: BoolSort) -> None:
        self._items.append(item)

    def __iter__(self) -> Iterator[BoolSort]:
        yield from self._items
