from __future__ import annotations

import typing


if typing.TYPE_CHECKING:
    from ._bool import BoolSort
    from ._dict import DictSort
    from ._float import FloatSort
    from ._func import FuncSort
    from ._int import IntSort
    from ._list import ListSort
    from ._pattern import PatternSort
    from ._proxy import ProxySort
    from ._set import SetSort
    from ._str import StrSort
    from ._var_tuple import VarTupleSort


P = typing.TypeVar('P', bound='type[ProxySort]')
Str = str


class Registry:
    # built-ins
    bool: type[BoolSort]
    int: type[IntSort]
    float: type[FloatSort]
    list: type[ListSort]
    set: type[SetSort]
    str: type[StrSort]
    tuple: type[VarTupleSort]
    dict: type[DictSort]

    # internal
    func: type[FuncSort]

    # stdlib
    pattern: type[PatternSort]

    _proxies: typing.Dict[Str, type[ProxySort]]

    def __init__(self) -> None:
        self._proxies = dict()

    def __getattr__(self, name: Str) -> type[ProxySort]:
        return self._proxies[name]

    def add(self, cls: P) -> P:
        self._proxies[cls.type_name.lower()] = cls
        return cls


types = Registry()
