import sre_constants
import sre_parse
import string
import typing

import z3

from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import types


if typing.TYPE_CHECKING:
    from .._context import Context
    from ._bool import BoolSort


@types.add
class PatternSort(ProxySort):
    module_name = 're'
    type_name = 'Pattern'
    methods = ProxySort.methods.copy()

    expr: z3.ReRef
    pattern: typing.Optional[str]

    def __init__(self, expr, pattern: str = None) -> None:
        assert z3.is_re(expr)
        self.expr = expr
        self.pattern = pattern

    @classmethod
    def var(cls, *, name: str, ctx: z3.Context) -> 'PatternSort':
        expr = z3.Const(
            name=name,
            sort=z3.ReSort(z3.StringSort(ctx=ctx)),
        )
        return cls(expr=expr)

    @classmethod
    def val(cls, pattern: str, flags: int = 0) -> 'PatternSort':
        parsed = sre_parse.parse(pattern, flags=flags)
        expr = cls._parse_pattern(parsed)
        return cls(expr=expr, pattern=pattern)

    @classmethod
    def _parse_pattern(cls, pattern: sre_parse.SubPattern) -> z3.ReRef:
        result = []
        for t_type, t_args in pattern.data:
            token = cls._parse_token(t_type, t_args)
            result.append(token)
        if not result:
            return z3.Re('')
        if len(result) == 1:
            return result[0]
        return z3.Concat(*result)

    @classmethod
    def _parse_token(cls, t_type: int, t_args) -> 'PatternSort':
        re_all = z3.Range(
            z3.Unit(z3.BitVecVal(0, 8)),
            z3.Unit(z3.BitVecVal(255, 8)),
        )

        if t_type == sre_constants.LITERAL:
            return z3.Re(chr(t_args))
        if t_type == sre_constants.NOT_LITERAL:
            return z3.Intersect(re_all, z3.Complement(z3.Re(chr(t_args))))
        if t_type == sre_constants.RANGE:
            lo, hi = t_args
            return z3.Range(chr(lo), chr(hi))
        if t_type == sre_constants.IN:
            subpatterns = []
            for st_type, st_args in t_args:
                subpatterns.append(cls._parse_token(st_type, st_args))
            return z3.Union(*subpatterns)
        if t_type == sre_constants.SUBPATTERN:
            return cls._parse_pattern(t_args[-1])
        if t_type == sre_constants.ANY and t_args is None:
            return z3.Intersect(re_all, z3.Complement(z3.Re('\n')))

        if t_type == sre_constants.MAX_REPEAT:
            start = t_args[0]
            end = t_args[1]
            sub_re = cls._parse_pattern(t_args[2])
            if end == sre_constants.MAXREPEAT:
                if start == 0:
                    return z3.Star(sub_re)
                if start == 1:
                    return z3.Plus(sub_re)
                return z3.Loop(sub_re, start)
            if start == 0 and end == 1:
                return z3.Option(sub_re)
            return z3.Loop(sub_re, start, end)

        if t_type == sre_constants.CATEGORY:
            # inclusive
            if t_args == sre_constants.CATEGORY_DIGIT:
                return z3.Range('0', '9')
            if t_args == sre_constants.CATEGORY_WORD:
                return z3.Union(
                    z3.Range('a', 'z'),
                    z3.Range('A', 'Z'),
                )
            if t_args == sre_constants.CATEGORY_SPACE:
                return z3.Union(*(z3.Re(ch) for ch in string.whitespace))

            # exclusive
            sub_re = None
            if t_args == sre_constants.CATEGORY_NOT_DIGIT:
                sub_re = cls._parse_token(t_type, sre_constants.CATEGORY_DIGIT)
            if t_args == sre_constants.CATEGORY_NOT_WORD:
                sub_re = cls._parse_token(t_type, sre_constants.CATEGORY_WORD)
            if t_args == sre_constants.CATEGORY_NOT_SPACE:
                sub_re = cls._parse_token(t_type, sre_constants.CATEGORY_SPACE)

            # there are more categories defined but they seem to be unused
            assert sub_re is not None, 'unknown re category'
            return z3.Intersect(re_all, z3.Complement(sub_re))

        raise UnsupportedError('cannot interpret regexp')

    @methods.add(name='fullmatch')
    def fullmatch(self, string: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(string, types.str):
            ctx.add_exception(TypeError, 'expected string or bytes-like object')
            return types.bool.val(False, ctx=ctx)
        return types.bool(expr=z3.InRe(string.expr, self.expr))

    @methods.add(name='match')
    def match(self, string: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(string, types.str):
            ctx.add_exception(TypeError, 'expected string or bytes-like object')
            return types.bool.val(False, ctx=ctx)
        rex = z3.Concat(
            self.expr,
            z3.Star(
                z3.Range(
                    z3.Unit(z3.BitVecVal(0, 8)),
                    z3.Unit(z3.BitVecVal(255, 8)),
                ),
            ),
        )
        return types.bool(expr=z3.InRe(string.expr, rex))
