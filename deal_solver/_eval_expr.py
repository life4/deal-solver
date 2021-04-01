# stdlib
import typing
from functools import partial

# external
import astroid
import z3

# app
from ._ast import get_full_name, infer
from ._context import Context
from ._exceptions import UnsupportedError
from ._funcs import FUNCTIONS
from ._proxies import (
    FloatSort, LambdaSort, ListSort, ProxySort, SetSort, and_expr,
    if_expr, not_expr, or_expr, random_name, unwrap, wrap,
)
from ._registry import HandlersRegistry


eval_expr: HandlersRegistry[ProxySort] = HandlersRegistry()

CONSTS: typing.Mapping[type, typing.Callable[..., ProxySort]]
CONSTS = {
    bool: z3.BoolVal,
    int: z3.IntVal,
    float: FloatSort.val,
    str: z3.StringVal,
}
COMAPARISON: typing.Mapping[str, str]
COMAPARISON = {
    '<':  'is_lt',
    '<=': 'is_le',
    '>':  'is_gt',
    '>=': 'is_ge',
    '==': 'is_eq',
    '!=': 'is_ne',
    'in': 'is_in',
}
BIN_OPERATIONS: typing.Mapping[str, str]
BIN_OPERATIONS = {
    # math
    '+':  'op_add',
    '-':  'op_sub',
    '*':  'op_mul',
    '/':  'op_div',
    '//': 'op_floor_div',
    '**': 'op_pow',
    '%':  'op_mod',
    '@':  'op_mat_mul',

    # bitwise
    '&':  'bit_and',
    '|':  'bit_or',
    '^':  'bit_xor',
    '<<': 'bit_lshift',
    '>>': 'bit_rshift',
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
    return wrap(converter(node.value, ctx=ctx.z3_ctx))


@eval_expr.register(astroid.BinOp)
def eval_bin_op(node: astroid.BinOp, ctx: Context) -> ProxySort:
    assert node.op
    op_name = BIN_OPERATIONS.get(node.op)
    assert op_name, 'unsupported binary operator'
    left = eval_expr(node=node.left, ctx=ctx)
    right = eval_expr(node=node.right, ctx=ctx)
    operation = getattr(left, op_name)
    try:
        result = operation(right, ctx=ctx)
    except z3.Z3Exception:
        raise UnsupportedError(f'cannot perform operation: {left.type_name}{node.op}{right.type_name}')
    except TypeError:
        raise UnsupportedError(f'cannot perform operation: {left.type_name}{node.op}{right.type_name}')
    return wrap(result)


@eval_expr.register(astroid.Compare)
def eval_compare(node: astroid.Compare, ctx: Context) -> ProxySort:
    left = wrap(eval_expr(node=node.left, ctx=ctx))
    for op, right_node in node.ops:
        assert op, 'missed comparison operator'
        op_name = COMAPARISON.get(op)
        assert op_name, 'unsupported comparison operator'

        right = wrap(eval_expr(node=right_node, ctx=ctx))
        # TODO: proper chain
        method = getattr(left, op_name)
        return method(right, ctx=ctx)
    raise RuntimeError('unreachable')  # pragma: no cover


@eval_expr.register(astroid.BoolOp)
def eval_bool_op(node: astroid.BoolOp, ctx: Context) -> ProxySort:
    assert node.op
    operation = BOOL_OPERATIONS.get(node.op)
    assert operation, 'unsupported binary boolean operation'
    assert node.values

    subnodes = []
    for subnode in node.values:
        right = eval_expr(node=subnode, ctx=ctx)
        if isinstance(right, ProxySort):
            right = right.as_bool
        subnodes.append(right)
    return operation(*subnodes)


@eval_expr.register(astroid.List)
def eval_list(node: astroid.List, ctx: Context) -> ProxySort:
    container = ListSort.make_empty()
    for subnode in node.elts:
        item = eval_expr(node=subnode, ctx=ctx)
        container = ListSort.append(container, item)
    return container


@eval_expr.register(astroid.Set)
def eval_set(node: astroid.Set, ctx: Context) -> ProxySort:
    container = SetSort.make_empty()
    for subnode in node.elts:
        item = eval_expr(node=subnode, ctx=ctx)
        container = SetSort.add(container, item)
    return container


@eval_expr.register(astroid.ListComp)
def eval_list_comp(node: astroid.ListComp, ctx: Context) -> ProxySort:
    if len(node.generators) > 1:
        raise UnsupportedError('to many loops inside list compr')

    comp: astroid.Comprehension
    comp = node.generators[0]

    items = unwrap(eval_expr(node=comp.iter, ctx=ctx))
    if comp.ifs:
        items = _compr_apply_ifs(ctx=ctx, comp=comp, items=items)
    items = _compr_apply_body(node=node, ctx=ctx, comp=comp, items=items)

    return wrap(items)


def _compr_apply_ifs(
    ctx: Context,
    comp: astroid.Comprehension,
    items: z3.Z3PPObject,
) -> z3.Z3PPObject:
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)

    index = z3.Int(random_name('index'))
    body_ctx = ctx.make_child()
    body_ctx.scope.set(
        name=comp.target.name,
        value=wrap(items[index]),
    )

    conds = []
    for cond_node in comp.ifs:
        cond = eval_expr(node=cond_node, ctx=body_ctx)
        conds.append(cond.as_bool.expr)

    f = z3.RecFunction(
        random_name('compr_cond'),
        z3.IntSort(ctx=ctx.z3_ctx), items.sort(),
    )
    if_body = z3.If(
        z3.And(*conds),
        z3.Unit(items[index]),
        z3.Empty(items.sort()),
    )
    z3.RecAddDefinition(f, index, z3.If(
        index == zero,
        if_body,
        f(index - one) + if_body,
    ))
    return f(z3.Length(items) - one)


def _compr_apply_body(
    node: astroid.ListComp,
    ctx: Context,
    comp: astroid.Comprehension,
    items: z3.Z3PPObject,
) -> z3.Z3PPObject:
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    index = z3.Int(random_name('index'))
    body_ctx = ctx.make_child()
    body_ctx.scope.set(
        name=comp.target.name,
        value=wrap(items[index]),
    )
    body_ref = unwrap(eval_expr(node=node.elt, ctx=body_ctx))

    f = z3.RecFunction(
        random_name('compr_body'),
        z3.IntSort(ctx=ctx.z3_ctx), z3.SeqSort(body_ref.sort()),
    )
    z3.RecAddDefinition(f, index, z3.If(
        index == zero,
        z3.Unit(body_ref),
        f(index - one) + z3.Unit(body_ref),
    ))
    return f(z3.Length(items) - one)


@eval_expr.register(astroid.Subscript)
def eval_getitem(node: astroid.Subscript, ctx: Context) -> ProxySort:
    value_ref = eval_expr(node=node.value, ctx=ctx)
    if not isinstance(value_ref, ListSort):
        raise UnsupportedError(value_ref.type_name, 'object is not subscriptable')

    if not isinstance(node.slice, astroid.Slice):
        item_ref = eval_expr(node=node.slice, ctx=ctx)
        return value_ref.get_item(item_ref)

    if node.slice.step:
        raise UnsupportedError('slice step is not supported')
    if node.slice.lower:
        lower_ref = eval_expr(node=node.slice.lower, ctx=ctx)
    else:
        lower_ref = z3.IntVal(0, ctx=ctx.z3_ctx)
    if node.slice.upper:
        upper_ref = eval_expr(node=node.slice.upper, ctx=ctx)
    else:
        upper_ref = value_ref.length
    return value_ref.get_slice(start=lower_ref, stop=upper_ref)


@eval_expr.register(astroid.Index)
def eval_index(node: astroid.Index, ctx: Context) -> ProxySort:
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
            return func

    # resolve built-in functions
    value = FUNCTIONS.get('builtins.' + node.name)
    if value is not None:
        return value

    raise UnsupportedError('cannot resolve name', node.name)


@eval_expr.register(astroid.Attribute)
def eval_attr(node: astroid.Attribute, ctx: Context):
    try:
        expr_ref = eval_expr(node=node.expr, ctx=ctx)
    except UnsupportedError:
        # resolve functions
        definitions = infer(node)
        if len(definitions) != 1:
            raise UnsupportedError('cannot resolve attribute', node.as_string())
        target = definitions[0]

        if isinstance(target, (astroid.FunctionDef, astroid.UnboundMethod)):
            target_name = '.'.join(get_full_name(target))
            func = FUNCTIONS.get(target_name)
            if func is None:
                raise UnsupportedError('no definition for', target_name)
            return func

        # resolve constants
        return eval_expr(node=target, ctx=ctx)

    # resolve methods
    if isinstance(expr_ref, ProxySort):
        target = 'builtins.{}.{}'.format(expr_ref.type_name, node.attrname)
        func = FUNCTIONS.get(target)
        if func is None:
            raise UnsupportedError('no definition for', target)
        return partial(func, expr_ref)


@eval_expr.register(astroid.UnaryOp)
def eval_unary_op(node: astroid.UnaryOp, ctx: Context) -> ProxySort:
    value_ref = eval_expr(node=node.operand, ctx=ctx)
    if node.op == '+':
        return value_ref.as_positive(ctx=ctx)
    if node.op == '-':
        return value_ref.as_negative(ctx=ctx)
    if node.op == '~':
        return value_ref.as_inverted(ctx=ctx)
    if node.op == 'not':
        return not_expr(value_ref)
    raise RuntimeError('unsupported unary operation')


@eval_expr.register(astroid.IfExp)
def eval_ternary_op(node: astroid.IfExp, ctx: Context) -> ProxySort:
    assert node.test is not None
    assert node.body is not None
    assert node.orelse is not None

    # execute child nodes
    test_ref = eval_expr(node=node.test, ctx=ctx)
    then_ref = eval_expr(node=node.body, ctx=ctx)
    else_ref = eval_expr(node=node.orelse, ctx=ctx)

    return if_expr(test_ref, then_ref, else_ref)


@eval_expr.register(astroid.Call)
def eval_call(node: astroid.Call, ctx: Context) -> ProxySort:
    if node.keywords:
        raise UnsupportedError('keyword function arguments are unsupported')

    call_args = []
    for arg_node in node.args:
        arg_node = eval_expr(node=arg_node, ctx=ctx)
        call_args.append(arg_node)

    value = eval_expr(node=node.func, ctx=ctx)
    if isinstance(value, astroid.FunctionDef):
        return _call_function(node=value, ctx=ctx, call_args=call_args)
    if not callable(value):
        raise UnsupportedError(value.type_name, 'object is not callable')

    if isinstance(node.func, astroid.Attribute):
        var_name = node.func.expr.as_string()
    else:
        var_name = node.func.as_string()

    return value(*call_args, ctx=ctx, var_name=var_name)


def _call_function(node: astroid.FunctionDef, ctx: Context, call_args=typing.List[z3.Z3PPObject]):
    # app
    from ._eval_contracts import eval_contracts
    from ._eval_stmt import eval_stmt

    # put arguments into the scope
    func_ctx = Context.make_empty(get_contracts=ctx.get_contracts, trace=ctx.trace)
    for arg, value in zip(node.args.args or [], call_args):
        func_ctx.scope.set(name=arg.name, value=value)

    # call the function
    eval_stmt(node=node, ctx=func_ctx)
    result = func_ctx.return_value
    if result is None:
        raise UnsupportedError('cannot find return value for', node.name)

    # we ask pre-conditions to be true
    # and promise post-condition to be true
    contracts = eval_contracts(func=node, ctx=func_ctx)
    ctx.expected.add(and_expr(*contracts.pre))
    ctx.given.add(and_expr(*contracts.post))

    return result


@eval_expr.register(astroid.Lambda)
def eval_lambda(node: astroid.Lambda, ctx: Context):
    return LambdaSort(
        ctx=ctx,
        args=node.args,
        body=node.body,
    )
