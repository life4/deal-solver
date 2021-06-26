import typing

import astroid
import z3

from ._annotations import ann2type
from ._ast import infer
from ._context import Context, ExceptionInfo, ReturnInfo
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError
from ._proxies import if_expr, or_expr, types
from ._registry import HandlersRegistry


eval_stmt: HandlersRegistry[None] = HandlersRegistry()


@eval_stmt.register(astroid.FunctionDef)
def eval_func(node: astroid.FunctionDef, ctx: Context) -> None:
    # if it is a recursive call, fake the function
    if node.name in ctx.trace:
        args = [v.expr for v in ctx.scope.layer.values()]
        # generate function signature
        sorts = [arg.sort() for arg in args]
        assert node.returns, 'cannot find type annotation for already executed func'
        sort = ann2type(name='_', node=node.returns, ctx=ctx.z3_ctx)
        assert sort is not None, 'cannot eval type annotation for already executed func'
        sorts.append(sort.sort())

        func = z3.Function(node.name, *sorts)
        proxy = type(sort)
        ctx.returns.add(ReturnInfo(
            value=proxy(func(*args)),
            cond=types.bool.val(True, ctx=ctx),
        ))
        return

    # otherwise, try to execute it
    with ctx.trace.guard(node.name):
        try:
            for statement in node.body:  # pragma: no cover
                eval_stmt(node=statement, ctx=ctx)
        except UnsupportedError as exc:
            ctx.skips.append(exc)


@eval_stmt.register(astroid.Assert)
def eval_assert(node: astroid.Assert, ctx: Context) -> None:
    assert node.test is not None, 'assert without condition'
    expr = eval_expr(node=node.test, ctx=ctx)
    expr = expr.m_bool(ctx=ctx)
    expr = or_expr(ctx.interrupted, expr, ctx=ctx)
    ctx.expected.add(expr)


@eval_stmt.register(astroid.Expr)
def eval_expr_stmt(node: astroid.Expr, ctx: Context) -> None:
    eval_expr(node=node.value, ctx=ctx)


@eval_stmt.register(astroid.Assign)
def eval_assign(node: astroid.Assign, ctx: Context) -> None:
    assert node.targets
    for target in node.targets:
        value_ref = eval_expr(node=node.value, ctx=ctx)
        # set item
        if isinstance(target, astroid.Subscript):
            if isinstance(target.slice, astroid.Slice):
                raise UnsupportedError('cannot set item for slice')
            key_ref = eval_expr(node=target.slice, ctx=ctx)
            target_ref = eval_expr(node=target.value, ctx=ctx)
            new_value = target_ref.m_setitem(key_ref, value_ref, ctx=ctx)
            if isinstance(target.value, astroid.Name):
                ctx.scope.set(name=target.value.name, value=new_value)
                continue
        # assign to a variable
        if isinstance(target, astroid.AssignName):
            ctx.scope.set(name=target.name, value=value_ref)
            continue
        raise UnsupportedError('cannot assign to', type(target).__name__)


@eval_stmt.register(astroid.Return)
def eval_return(node: astroid.Return, ctx: Context) -> None:
    ctx.returns.add(ReturnInfo(
        value=eval_expr(node=node.value, ctx=ctx),
        cond=ctx.interrupted.m_not(ctx=ctx),
    ))


@eval_stmt.register(astroid.If)
def eval_if_else(node: astroid.If, ctx: Context) -> None:
    assert node.test
    assert node.body

    test_ref = eval_expr(node=node.test, ctx=ctx)

    ctx_then = ctx.make_child()
    for subnode in node.body:
        eval_stmt(node=subnode, ctx=ctx_then)
    ctx_else = ctx.make_child()
    for subnode in (node.orelse or []):
        eval_stmt(node=subnode, ctx=ctx_else)

    # update variables
    changed_vars = set(ctx_then.scope.layer) | set(ctx_else.scope.layer)
    for var_name in changed_vars:
        val_then = ctx_then.scope.get(name=var_name)
        val_else = ctx_else.scope.get(name=var_name)
        if val_then is None or val_else is None:
            continue
        value = if_expr(test_ref, val_then, val_else, ctx=ctx)
        ctx.scope.set(name=var_name, value=value)

    # update new assertions
    true = types.bool.val(True, ctx=ctx)
    for constr in ctx_then.expected.layer:
        ctx.expected.add(if_expr(test_ref, constr, true, ctx=ctx))
    for constr in ctx_else.expected.layer:
        ctx.expected.add(if_expr(test_ref, true, constr, ctx=ctx))

    # update new exceptions
    false = types.bool.val(False, ctx=ctx)
    for exc in ctx_then.exceptions.layer:
        ctx.exceptions.add(ExceptionInfo(
            name=exc.name,
            names=exc.names,
            cond=if_expr(test_ref, exc.cond, false, ctx=ctx),
            message=exc.message,
        ))
    for exc in ctx_else.exceptions.layer:
        ctx.exceptions.add(ExceptionInfo(
            name=exc.name,
            names=exc.names,
            cond=if_expr(test_ref, false, exc.cond, ctx=ctx),
            message=exc.message,
        ))

    # update new return statements
    false = types.bool.val(False, ctx=ctx)
    for ret in ctx_then.returns.layer:
        ctx.returns.add(ReturnInfo(
            value=ret.value,
            cond=if_expr(test_ref, ret.cond, false, ctx=ctx),
        ))
    for ret in ctx_else.returns.layer:
        ctx.returns.add(ReturnInfo(
            value=ret.value,
            cond=if_expr(test_ref, false, ret.cond, ctx=ctx),
        ))


@eval_stmt.register(astroid.Raise)
def eval_raise(node: astroid.Raise, ctx: Context) -> None:
    names: typing.Set[str] = set()
    for exc in (node.exc, node.cause):
        if exc is None:
            continue
        names.update(_get_all_bases(exc))
    ctx.exceptions.add(ExceptionInfo(
        name=next(_get_all_bases(node.exc)),
        names=names,
        cond=ctx.interrupted.m_not(ctx=ctx),
    ))


def _get_all_bases(node) -> typing.Iterator[str]:
    def_nodes = infer(node)
    for def_node in def_nodes:
        if isinstance(def_node, astroid.Instance):
            def_node = def_node._proxied
        if isinstance(node, astroid.Name):
            yield node.name

        if not isinstance(def_node, astroid.ClassDef):
            continue
        yield def_node.name
        for parent_node in def_node.bases:
            if isinstance(parent_node, astroid.Name):
                yield from _get_all_bases(parent_node)


@eval_stmt.register(astroid.Global)
@eval_stmt.register(astroid.ImportFrom)
@eval_stmt.register(astroid.Import)
@eval_stmt.register(astroid.Pass)
def eval_skip(node, ctx: Context) -> None:
    pass
