import string
import sre_parse
import sre_constants
import typing

import z3

from ._proxy import ProxySort
from ._registry import registry
from .._exceptions import UnsupportedError


if typing.TYPE_CHECKING:
    from ._bool import BoolSort
    from .._context import Context


@registry.add
class PatternSort(ProxySort):
    module_name = 're'
    type_name = 'Pattern'
    methods = ProxySort.methods.copy()

    expr: z3.ReRef
    pattern: str

    def __init__(self, expr, pattern: str) -> None:
        assert z3.is_re(expr)
        self.expr = expr
        self.pattern = pattern

    @classmethod
    def from_str(cls, pattern: str, flags: int) -> 'PatternSort':
        parsed = sre_parse.parse(pattern, flags=flags)
        expr = cls._parse_pattern(parsed)
        return cls(expr=expr, pattern=pattern)

    @classmethod
    def _parse_pattern(cls, pattern: sre_parse.SubPattern):
        result = []
        for t_type, t_args in pattern.data:
            token = cls._parse_token(t_type, t_args)
            result.append(token)
        if not result:
            return z3.Re("")
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
        if t_type == sre_constants.ANY and t_args is None:
            return z3.Intersect(re_all, z3.Complement(z3.Re('\n')))
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
            if sub_re is not None:
                return z3.Intersect(re_all, z3.Complement(sub_re))

        raise UnsupportedError('cannot interpret regexp')

    @methods.add(name='fullmatch')
    def fullmatch(self, string: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(string, registry.str):
            ctx.add_exception(TypeError, "expected string or bytes-like object")
            return registry.bool.val(False)
        return registry.bool(expr=z3.InRe(string.expr, self.expr))

    @methods.add(name='match')
    def match(self, string: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(string, registry.str):
            ctx.add_exception(TypeError, "expected string or bytes-like object")
            return registry.bool.val(False)
        rex = z3.Concat(
            self.expr,
            z3.Star(
                z3.Range(
                    z3.Unit(z3.BitVecVal(0, 8)),
                    z3.Unit(z3.BitVecVal(255, 8)),
                )
            ),
        )
        return registry.bool(expr=z3.InRe(string.expr, rex))
