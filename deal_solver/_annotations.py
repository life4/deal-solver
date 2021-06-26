import typing
from types import MappingProxyType

import astroid
import z3

from ._ast import get_full_name, get_name, infer
from ._proxies import ProxySort, VarTupleSort, types
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
    arity: int


GENERICS: typing.Mapping[str, Generic]
GENERICS = MappingProxyType({
    'list': Generic(type=types.list, arity=1),
    'set':  Generic(type=types.set, arity=1),
    'dict': Generic(type=types.dict, arity=2),
})


def ann2type(*, name: str, node: AstNode, ctx: z3.Context) -> MaybeSort:
    if isinstance(node, astroid.Attribute):
        return _sort_from_attr(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Name):
        return _sort_from_name(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Const) and type(node.value) is str:
        return _sort_from_str(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Subscript):
        return _sort_from_getattr(name=name, node=node, ctx=ctx)
    return None


def _sort_from_attr(*, name: str, node: astroid.Attribute, ctx: z3.Context) -> MaybeSort:
    definitions = infer(node)
    if len(definitions) != 1:
        return None
    module_name, _ = get_full_name(definitions[0])
    if module_name not in {'typing', 'builtins'}:
        return None

    sort = SIMPLE_SORTS.get(node.attrname)
    if sort is None:
        return None
    return sort.var(name=name, ctx=ctx)


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
    # check the module name
    definitions = infer(node.value)
    if len(definitions) != 1:
        return None
    module_name, _ = get_full_name(definitions[0])
    if module_name not in {'typing', 'builtins'}:
        return None

    sl = node.slice
    if isinstance(sl, astroid.Index):  # pragma: no cover
        sl = sl.value
    if isinstance(sl, astroid.Tuple):
        nodes = sl.elts
    else:
        nodes = [sl]

    type_name = get_name(node.value) or ''
    type_name = type_name.split('.')[-1]
    type_name = ALIASES.get(type_name, type_name)

    if type_name == 'tuple':
        # variable size tuple
        if _is_var_tuple(nodes):
            subtype = ann2type(name=name, node=nodes[0], ctx=ctx)
            if subtype is None:
                return None
            return VarTupleSort.var(subtype, name=name, ctx=ctx)
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
    return generic.type.var(*subtypes, name=name, ctx=ctx)


def _is_var_tuple(nodes: list) -> bool:
    if len(nodes) != 2:
        return False
    last = nodes[-1]
    if isinstance(last, astroid.Ellipsis):  # pragma: no cover
        return True
    if isinstance(last, astroid.Const):
        return last.value is Ellipsis
    return False
