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
    tuple: typing.Type['VarTupleSort']
    dict: typing.Type['DictSort']

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
        self._proxies[cls.type_name.lower()] = cls
        return cls


types = Registry()
