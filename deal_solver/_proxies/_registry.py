# stdlib
import typing


if typing.TYPE_CHECKING:
    # app
    from ._bool import BoolSort
    from ._float import FloatSort
    from ._func import FuncSort
    from ._int import IntSort
    from ._list import ListSort
    from ._pattern import PatternSort
    from ._proxy import ProxySort
    from ._set import SetSort
    from ._str import StrSort


P = typing.TypeVar('P', bound=typing.Type['ProxySort'])
Str = str


class Registry:
    # built-ins
    bool: typing.Type['BoolSort']
    int: typing.Type['IntSort']
    float: typing.Type['FloatSort']
    list: typing.Type['ListSort']
    set: typing.Type['SetSort']
    str: typing.Type['StrSort']

    # internal
    func: typing.Type['FuncSort']

    # stdlib
    pattern: typing.Type['PatternSort']

    _proxies: typing.Dict[Str, typing.Type['ProxySort']]

    def __init__(self) -> None:
        self._proxies = dict()

    def __getattr__(self, name: Str) -> typing.Type['ProxySort']:
        return self._proxies[name]

    def add(self, cls: P) -> P:
        self._proxies[cls.type_name] = cls
        return cls


registry = Registry()
