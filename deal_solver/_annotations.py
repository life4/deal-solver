import typing
from types import MappingProxyType

import astroid
import z3

from ._ast import get_full_name, get_name, infer
from ._proxies import types, ProxySort, VarTupleSort
from ._types import AstNode


SIMPLE_SORTS: typing.Mapping[str, typing.Type[ProxySort]]
SIMPLE_SORTS = MappingProxyType({
    'bool':     types.bool,
    'int':      types.int,
    'float':    types.float,
    'str':      types.str,
    'Pattern':  types.pattern,
})
ALIASES: typing.Mapping[str, str]
ALIASES = MappingProxyType({
    'Tuple': 'tuple',
    'List':  'list',
    'Dict':  'dict',
    'Set':   'set',

    'Sequence': 'list',
    'Iterable': 'list',
    'Sized': 'list',
    'Mapping': 'dict',
    'MutableMapping': 'dict',
    'AnyStr': 'str',
    'FrozenSet': 'set',
})
MaybeSort = typing.Optional[ProxySort]


class Generic(typing.NamedTuple):
    type: typing.Type[ProxySort]
    sort: typing.Callable
    arity: int


GENERICS: typing.Mapping[str, Generic]
GENERICS = MappingProxyType({
    'list': Generic(type=types.list, sort=z3.SeqSort, arity=1),
    'set':  Generic(type=types.set, sort=z3.SetSort, arity=1),
    # 'dict': Generic(type=types.dict, sort=z3.ArraySort, arity=2),
})


def ann2type(*, name: str, node: AstNode, ctx: z3.Context) -> MaybeSort:
    if isinstance(node, astroid.Name):
        return _sort_from_name(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Const) and type(node.value) is str:
        return _sort_from_str(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Subscript):
        return _sort_from_getattr(name=name, node=node, ctx=ctx)
    return None


def _sort_from_name(*, name: str, node: astroid.Name, ctx: z3.Context) -> MaybeSort:
    type_name = ALIASES.get(node.name, node.name)
    sort = SIMPLE_SORTS.get(type_name)
    if sort is None:
        return None
    return sort.var(name=name, ctx=ctx)


def _sort_from_str(*, name: str, node: astroid.Const, ctx: z3.Context) -> MaybeSort:
    type_name = ALIASES.get(node.value, node.value)
    sort = SIMPLE_SORTS.get(type_name)
    if sort is None:
        return None
    return sort.var(name=name, ctx=ctx)


def _sort_from_getattr(*, name: str, node: astroid.Subscript, ctx: z3.Context) -> MaybeSort:
    if not isinstance(node.slice, astroid.Index):
        return None

    # check the module name
    definitions = infer(node.value)
    if len(definitions) != 1:
        return None
    module_name, _ = get_full_name(definitions[0])
    if module_name != 'typing' and module_name != 'builtins':
        return None

    if isinstance(node.slice.value, astroid.Tuple):
        nodes = node.slice.value.elts
    else:
        nodes = [node.slice.value]

    type_name = get_name(node.value) or ''
    type_name = ALIASES.get(type_name, type_name)

    if type_name == 'tuple':
        # variable size tuple
        if len(nodes) == 2 and isinstance(nodes[-1], astroid.Ellipsis):
            subtype = ann2type(name=name, node=nodes[0], ctx=ctx)
            if subtype is None:
                return None
            sort = z3.SeqSort(subtype.sort())
            return VarTupleSort(expr=z3.Const(name=name, sort=sort))
        return None

    generic = GENERICS.get(type_name)
    if generic is None:
        return None
    if len(nodes) != generic.arity:
        return None

    subtypes = []
    for node in nodes:
        subtype = ann2type(name=name, node=node, ctx=ctx)
        if subtype is None:
            return None
        subtypes.append(subtype)
    subsorts = [subtype.sort() for subtype in subtypes]
    sort = generic.sort(*subsorts)
    return generic.type(expr=z3.Const(name=name, sort=sort))
