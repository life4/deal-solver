# external
import typing
import astroid
import z3

# app
from ._annotations import ann2sort
from ._ast import infer
from ._context import Context, ExceptionInfo, ReturnInfo
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError
from ._proxies import ProxySort, if_expr, unwrap, BoolSort, not_expr
from ._registry import HandlersRegistry


eval_stmt: HandlersRegistry[None] = HandlersRegistry()


@eval_stmt.register(astroid.FunctionDef)
def eval_func(node: astroid.FunctionDef, ctx: Context) -> None:
    # if it is a recursive call, fake the function
    if node.name in ctx.trace:
        args = [unwrap(v) for v in ctx.scope.layer.values()]
        # generate function signature
        sorts = [arg.sort() for arg in args]
        if not node.returns:
            raise UnsupportedError('no return type annotation for', node.name)
        sorts.append(ann2sort(node.returns, ctx=ctx.z3_ctx))

        func = z3.Function(node.name, *sorts)
        ctx.returns.add(ReturnInfo(
            value=func(*args),
            cond=BoolSort.val(True)
        ))
        return

    # otherwise, try to execute it
    with ctx.trace.guard(node.name):
        try:
            for statement in node.body:
                eval_stmt(node=statement, ctx=ctx)
        except UnsupportedError as exc:
            ctx.skips.append(exc)


@eval_stmt.register(astroid.Assert)
def eval_assert(node: astroid.Assert, ctx: Context) -> None:
    assert node.test is not None, 'assert without condition'
    expr = eval_expr(node=node.test, ctx=ctx)
    if isinstance(expr, ProxySort):
        expr = expr.as_bool
    true = BoolSort.val(True)
    expr = if_expr(ctx.interrupted, true, expr, ctx=ctx.z3_ctx)
    ctx.expected.add(expr)


@eval_stmt.register(astroid.Expr)
def eval_expr_stmt(node: astroid.Expr, ctx: Context) -> None:
    eval_expr(node=node.value, ctx=ctx)


@eval_stmt.register(astroid.Assign)
def eval_assign(node: astroid.Assign, ctx: Context) -> None:
    if not node.targets:
        raise UnsupportedError('assignment to an empty target')
    if len(node.targets) > 1:
        raise UnsupportedError('multiple assignment')
    target = node.targets[0]
    if not isinstance(target, astroid.AssignName):
        raise UnsupportedError('assignment target', type(target))

    value_ref = eval_expr(node=node.value, ctx=ctx)
    ctx.scope.set(name=target.name, value=value_ref)


@eval_stmt.register(astroid.Return)
def eval_return(node: astroid.Return, ctx: Context) -> None:
    ctx.returns.add(ReturnInfo(
        value=eval_expr(node=node.value, ctx=ctx),
        cond=not_expr(ctx.interrupted),
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
            raise UnsupportedError('unbound variable', var_name)

        value = if_expr(test_ref, val_then, val_else)
        ctx.scope.set(name=var_name, value=value)

    # update new assertions
    true = BoolSort.val(True)
    for constr in ctx_then.expected.layer:
        ctx.expected.add(if_expr(test_ref, constr, true))
    for constr in ctx_else.expected.layer:
        ctx.expected.add(if_expr(test_ref, true, constr))

    # update new exceptions
    false = BoolSort.val(False)
    for exc in ctx_then.exceptions.layer:
        ctx.exceptions.add(ExceptionInfo(
            names=exc.names,
            cond=if_expr(test_ref, exc.cond, false),
        ))
    for exc in ctx_else.exceptions.layer:
        ctx.exceptions.add(ExceptionInfo(
            names=exc.names,
            cond=if_expr(test_ref, false, exc.cond),
        ))

    # update new return statements
    false = BoolSort.val(False)
    for ret in ctx_then.returns.layer:
        ctx.returns.add(ReturnInfo(
            value=ret.value,
            cond=if_expr(test_ref, ret.cond, false),
        ))
    for ret in ctx_else.returns.layer:
        ctx.returns.add(ReturnInfo(
            value=ret.value,
            cond=if_expr(test_ref, false, ret.cond),
        ))


@eval_stmt.register(astroid.Raise)
def eval_raise(node: astroid.Raise, ctx: Context) -> None:
    names: typing.Set[str] = set()
    for exc in (node.exc, node.cause):
        if exc is None:
            continue
        names.update(_get_all_bases(exc))
    ctx.exceptions.add(ExceptionInfo(
        names=names,
        cond=not_expr(ctx.interrupted),
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
