import typing

import astroid
import z3

from ._ast import get_full_name, infer
from ._context import Context
from ._exceptions import UnsupportedError
from ._funcs import FUNCTIONS
from ._proxies import (
    DictSort, FuncSort, LambdaSort, ProxySort, UntypedDictSort, UntypedListSort,
    UntypedVarTupleSort, and_expr, if_expr, or_expr, random_name, types,
)
from ._registry import HandlersRegistry


eval_expr: HandlersRegistry[ProxySort] = HandlersRegistry()

CONSTS: typing.Mapping[type, typing.Callable[..., ProxySort]]
CONSTS = {
    bool: types.bool.val,
    int: types.int.val,
    float: types.float.val,
    str: types.str.val,
}
COMAPARISON: typing.Mapping[str, str]
COMAPARISON = {
    '<':  '__lt__',
    '<=': '__le__',
    '>':  '__gt__',
    '>=': '__ge__',
    '==': '__eq__',
    '!=': '__ne__',
    'in': 'in',
    'not in': 'not in',
}
BIN_OPERATIONS: typing.Mapping[str, str]
BIN_OPERATIONS = {
    # math
    '+':  '__add__',
    '-':  '__sub__',
    '*':  '__mul__',
    '/':  '__truediv__',
    '//': '__floordiv__',
    '**': '__pow__',
    '%':  '__mod__',
    '@':  '__matmul__',

    # bitwise
    '&':  '__and__',
    '|':  '__or__',
    '^':  '__xor__',
    '<<': '__lshift__',
    '>>': '__rshift__',
}
BOOL_OPERATIONS: typing.Mapping[str, typing.Callable[..., ProxySort]]
BOOL_OPERATIONS = {
    'and': and_expr,
    'or': or_expr,
}


@eval_expr.register(astroid.Const)
def eval_const(node: astroid.Const, ctx: Context) -> ProxySort:
    t = type(node.value)
    converter = CONSTS.get(t)
    if not converter:
        raise UnsupportedError('unsupported constant', repr(node.value))
    return converter(node.value, ctx=ctx)


@eval_expr.register(astroid.BinOp)
def eval_bin_op(node: astroid.BinOp, ctx: Context) -> ProxySort:
    assert node.op
    op_name = BIN_OPERATIONS.get(node.op)
    assert op_name, 'unsupported binary operator'
    left = eval_expr(node=node.left, ctx=ctx)
    right = eval_expr(node=node.right, ctx=ctx)
    method = left.m_getattr(op_name, ctx=ctx)
    result = method.m_call(right, ctx=ctx)
    return result


@eval_expr.register(astroid.Compare)
def eval_compare(node: astroid.Compare, ctx: Context) -> ProxySort:
    left = eval_expr(node=node.left, ctx=ctx)
    for op, right_node in node.ops:
        assert op, 'missed comparison operator'
        op_name = COMAPARISON.get(op)
        if not op_name:
            raise UnsupportedError('unsupported comparison operator', op)

        right = eval_expr(node=right_node, ctx=ctx)
        # TODO: proper chain
        method = left.m_getattr(op_name, ctx=ctx)
        return method.m_call(right, ctx=ctx)
    raise RuntimeError('unreachable')


@eval_expr.register(astroid.BoolOp)
def eval_bool_op(node: astroid.BoolOp, ctx: Context) -> ProxySort:
    assert node.op
    operation = BOOL_OPERATIONS.get(node.op)
    assert operation, 'unsupported binary boolean operation'
    assert node.values

    subnodes = []
    for subnode in node.values:
        right = eval_expr(node=subnode, ctx=ctx)
        subnodes.append(right.m_bool(ctx=ctx))
    return operation(*subnodes, ctx=ctx)


@eval_expr.register(astroid.List)
def eval_list(node: astroid.List, ctx: Context) -> ProxySort:
    if not node.elts:
        return UntypedListSort()
    items = []
    for subnode in node.elts:
        items.append(eval_expr(node=subnode, ctx=ctx))
    return types.list.val(items, ctx=ctx)


@eval_expr.register(astroid.Set)
def eval_set(node: astroid.Set, ctx: Context) -> ProxySort:
    items = []
    for subnode in node.elts:
        items.append(eval_expr(node=subnode, ctx=ctx))
    return types.set.val(items, ctx=ctx)


@eval_expr.register(astroid.Dict)
def eval_dict(node: astroid.Dict, ctx: Context) -> ProxySort:
    container: DictSort = UntypedDictSort()
    for key_node, val_node in node.items:
        key = eval_expr(node=key_node, ctx=ctx)
        val = eval_expr(node=val_node, ctx=ctx)
        container = container.m_setitem(key=key, value=val, ctx=ctx)
    return container


@eval_expr.register(astroid.Tuple)
def eval_tuple(node: astroid.Tuple, ctx: Context) -> ProxySort:
    if not node.elts:
        return UntypedVarTupleSort()
    items = []
    for subnode in node.elts:
        items.append(eval_expr(node=subnode, ctx=ctx))
    return types.tuple.val(items, ctx=ctx)


@eval_expr.register(astroid.ListComp)
def eval_list_comp(node: astroid.ListComp, ctx: Context) -> ProxySort:
    if len(node.generators) > 1:
        raise UnsupportedError('to many loops inside list compr')

    comp: astroid.Comprehension
    comp = node.generators[0]

    items = eval_expr(node=comp.iter, ctx=ctx)
    if comp.ifs:
        items = _compr_apply_ifs(ctx=ctx, comp=comp, items=items)
    items = _compr_apply_body(node=node, ctx=ctx, comp=comp, items=items)
    return items


def _compr_apply_ifs(
    ctx: Context,
    comp: astroid.Comprehension,
    items: ProxySort,
) -> ProxySort:
    if not isinstance(items, (types.list, types.tuple)):
        raise UnsupportedError(f'cannot iterate over {items.type_name}')
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)

    index = z3.Int(random_name('index'))
    body_ctx = ctx.make_child()
    body_ctx.scope.set(
        name=comp.target.name,
        value=items.m_getitem(types.int(index), ctx=ctx.make_child()),
    )

    conds = []
    for cond_node in comp.ifs:
        cond = eval_expr(node=cond_node, ctx=body_ctx)
        conds.append(cond.m_bool(ctx=ctx).expr)

    f = z3.RecFunction(
        random_name('compr_cond'),
        z3.IntSort(ctx=ctx.z3_ctx), items.sort(),
    )
    if_body = z3.If(
        z3.And(*conds),
        z3.Unit(items.m_getitem(types.int(index), ctx=ctx.make_child()).expr),
        z3.Empty(items.sort()),
    )
    z3.RecAddDefinition(f, index, z3.If(
        index == zero,
        if_body,
        f(index - one) + if_body,
    ))
    expr = f(z3.Length(items.expr) - one)
    return types.list(expr=expr, subtypes=items.subtypes)


def _compr_apply_body(
    node: astroid.ListComp,
    ctx: Context,
    comp: astroid.Comprehension,
    items: ProxySort,
) -> ProxySort:
    if not isinstance(items, (types.list, types.tuple)):
        raise UnsupportedError(f'cannot iterate over {items.type_name}')
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    index = z3.Int(random_name('index'))
    body_ctx = ctx.make_child()
    body_ctx.scope.set(
        name=comp.target.name,
        value=items.m_getitem(types.int(index), ctx=ctx.make_child()),
    )
    body_ref = eval_expr(node=node.elt, ctx=body_ctx).expr

    f = z3.RecFunction(
        random_name('compr_body'),
        z3.IntSort(ctx=ctx.z3_ctx), z3.SeqSort(body_ref.sort()),
    )
    z3.RecAddDefinition(f, [index], z3.If(
        index == zero,
        z3.Unit(body_ref),
        f(index - one) + z3.Unit(body_ref),
    ))
    expr = f(z3.Length(items.expr) - one)
    return types.list(expr=expr, subtypes=items.subtypes)


@eval_expr.register(astroid.Subscript)
def eval_getitem(node: astroid.Subscript, ctx: Context) -> ProxySort:
    value_ref = eval_expr(node=node.value, ctx=ctx)

    if not isinstance(node.slice, astroid.Slice):
        item_ref = eval_expr(node=node.slice, ctx=ctx)
        return value_ref.m_getitem(item_ref, ctx=ctx)

    if node.slice.step:
        raise UnsupportedError('slice step is not supported')
    if node.slice.lower:
        lower_ref = eval_expr(node=node.slice.lower, ctx=ctx)
    else:
        lower_ref = types.int(z3.IntVal(0, ctx=ctx.z3_ctx))
    if node.slice.upper:
        upper_ref = eval_expr(node=node.slice.upper, ctx=ctx)
    else:
        upper_ref = value_ref.m_len(ctx=ctx)
    return value_ref.get_slice(start=lower_ref, stop=upper_ref, ctx=ctx)


@eval_expr.register(astroid.Index)
def eval_index(node: astroid.Index, ctx: Context) -> ProxySort:  # pragma: no cover
    return eval_expr(node=node.value, ctx=ctx)


@eval_expr.register(astroid.Name)
def eval_name(node: astroid.Name, ctx: Context) -> ProxySort:
    # resolve local vars
    value = ctx.scope.get(node.name)
    if value is not None:
        return value

    # resolve definitions
    inferred = infer(node)
    if inferred:
        func = inferred[0]
        if isinstance(func, astroid.FunctionDef) and func.body:
            return FuncSort(func)

    # resolve built-in functions
    value = FUNCTIONS.get('builtins.' + node.name)
    if value is not None:
        return FuncSort(value)

    raise UnsupportedError('cannot resolve name', node.name)


@eval_expr.register(astroid.Attribute)
def eval_attr(node: astroid.Attribute, ctx: Context) -> ProxySort:
    try:
        expr_ref = eval_expr(node=node.expr, ctx=ctx)
    except UnsupportedError:
        # resolve functions defined outside of the scope
        definitions = infer(node)
        if not definitions:
            raise UnsupportedError('cannot resolve attribute', node.as_string())
        target = definitions[0]

        if isinstance(target, (astroid.FunctionDef, astroid.UnboundMethod)):
            target_name = '.'.join(get_full_name(target))
            func = FUNCTIONS.get(target_name)
            if func is None:
                raise UnsupportedError('no definition for', target_name)
            return FuncSort(func)

        # resolve constants defined outside of the scope
        return eval_expr(node=target, ctx=ctx)

    return expr_ref.m_getattr(node.attrname, ctx=ctx)


@eval_expr.register(astroid.UnaryOp)
def eval_unary_op(node: astroid.UnaryOp, ctx: Context) -> ProxySort:
    value_ref = eval_expr(node=node.operand, ctx=ctx)
    if node.op == '+':
        return value_ref.m_pos(ctx=ctx)
    if node.op == '-':
        return value_ref.m_neg(ctx=ctx)
    if node.op == '~':
        return value_ref.m_inv(ctx=ctx)
    if node.op == 'not':
        return value_ref.m_not(ctx=ctx)
    raise RuntimeError('unreachable')


@eval_expr.register(astroid.IfExp)
def eval_ternary_op(node: astroid.IfExp, ctx: Context) -> ProxySort:
    assert node.test is not None
    assert node.body is not None
    assert node.orelse is not None

    # execute child nodes
    test_ref = eval_expr(node=node.test, ctx=ctx)
    then_ref = eval_expr(node=node.body, ctx=ctx)
    else_ref = eval_expr(node=node.orelse, ctx=ctx)

    return if_expr(test_ref, then_ref, else_ref, ctx=ctx)


@eval_expr.register(astroid.Call)
def eval_call(node: astroid.Call, ctx: Context) -> ProxySort:
    call_args = []
    for arg_node in node.args:
        arg_node = eval_expr(node=arg_node, ctx=ctx)
        call_args.append(arg_node)

    call_kwargs = {}
    if node.keywords:
        for keyword in node.keywords:
            assert isinstance(keyword, astroid.Keyword)
            if not keyword.arg:
                raise UnsupportedError('dict unpacking is unsupported')
            call_kwargs[keyword.arg] = eval_expr(node=keyword.value, ctx=ctx)

    value = eval_expr(node=node.func, ctx=ctx)
    if isinstance(node.func, astroid.Attribute):
        var_name = node.func.expr.as_string()
    else:
        var_name = node.func.as_string()
    return value.m_call(*call_args, ctx=ctx, var_name=var_name, **call_kwargs)


@eval_expr.register(astroid.Lambda)
def eval_lambda(node: astroid.Lambda, ctx: Context) -> LambdaSort:
    return LambdaSort(
        ctx=ctx,
        args=node.args,
        body=node.body,
    )
