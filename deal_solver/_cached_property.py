from __future__ import annotations

from typing import Any, Callable, Generic, TypeVar, overload


T = TypeVar('T')


class cached_property(Generic[T]):  # noqa: N801
    func: Callable[[Any, Any], T]

    def __init__(self, func: Callable[[Any], T]) -> None:
        self.func = func  # type: ignore

    @overload
    def __get__(self, instance: None, owner: type[Any] | None = ...) -> cached_property[T]:
        pass

    @overload
    def __get__(self, instance, owner: type[Any] | None = ...) -> T:
        pass

    def __get__(self, obj, cls):
        if obj is None:
            return self
        value = self.func(obj)  # type: ignore
        obj.__dict__[self.func.__name__] = value
        return value
