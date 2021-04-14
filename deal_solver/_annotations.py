# stdlib
import typing
from types import MappingProxyType

# external
import astroid
import z3

# app
from ._ast import get_full_name, get_name, infer
from ._proxies import FloatSort, ProxySort, VarTupleSort, wrap, ListSort, SetSort
from ._types import AstNode


SIMPLE_SORTS = MappingProxyType({
    'bool': z3.BoolSort,
    'int': z3.IntSort,
    'float': FloatSort.sort,
    'str': z3.StringSort,
})
GENERIC_TYPES: typing.Mapping[str, typing.Type[ProxySort]]
GENERIC_TYPES = MappingProxyType({
    'list': ListSort,
    'set': SetSort,
})
GENERIC_SORTS: typing.Mapping[str, typing.Callable]
GENERIC_SORTS = MappingProxyType({
    'list': z3.SeqSort,
    'set': z3.SetSort,
})
MaybeSort = typing.Optional[ProxySort]


def ann2type(*, name: str, node: AstNode, ctx: z3.Context) -> MaybeSort:
    if isinstance(node, astroid.Index):
        return ann2type(name=name, node=node.value, ctx=ctx)
    if isinstance(node, astroid.Name):
        return _sort_from_name(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Const) and type(node.value) is str:
        return _sort_from_str(name=name, node=node, ctx=ctx)
    if isinstance(node, astroid.Subscript):
        return _sort_from_getattr(name=name, node=node, ctx=ctx)
    return None


def _sort_from_name(*, name: str, node: astroid.Name, ctx: z3.Context) -> MaybeSort:
    sort = SIMPLE_SORTS.get(node.name)
    if sort is None:
        return None
    return wrap(z3.Const(name=name, sort=sort(ctx=ctx)))


def _sort_from_str(*, name: str, node: astroid.Const, ctx: z3.Context) -> MaybeSort:
    sort = SIMPLE_SORTS.get(node.value)
    if sort is None:
        return None
    return wrap(z3.Const(name=name, sort=sort(ctx=ctx)))


def _sort_from_getattr(*, name: str, node: astroid.Subscript, ctx: z3.Context) -> MaybeSort:
    if not isinstance(node.slice, astroid.Index):
        return None
    definitions = infer(node.value)
    if len(definitions) != 1:
        return None

    module_name, _ = get_full_name(definitions[0])
    if module_name != 'typing' and module_name != 'builtins':
        return None

    type_name = (get_name(node.value) or '').lower()
    if type_name == 'tuple':
        if isinstance(node.slice.value, astroid.Tuple):
            nodes = node.slice.value.elts
            # variable size tuple
            if isinstance(nodes[-1], astroid.Ellipsis):
                subtype = ann2type(name=name, node=nodes[0], ctx=ctx)
                if subtype is None:
                    return None
                sort = z3.SeqSort(subtype.sort())
                return VarTupleSort(expr=z3.Const(name=name, sort=sort))
        return None

    gtype = GENERIC_TYPES.get(type_name)
    if gtype is None:
        return None

    subtype = ann2type(name=name, node=node.slice, ctx=ctx)
    if subtype is None:
        return None
    sort = GENERIC_SORTS[type_name](subtype.sort())
    return gtype(expr=z3.Const(name=name, sort=sort))
