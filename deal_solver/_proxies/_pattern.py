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
    expr: z3.ReRef
    type_name = 'Pattern'

    def __init__(self, expr) -> None:
        assert z3.is_re(expr)
        self.expr = expr

    @classmethod
    def from_str(cls, pattern: str, flags: int) -> 'PatternSort':
        parsed = sre_parse.parse(pattern, flags=flags)
        expr = cls._parse_pattern(parsed)
        return cls(expr=expr)

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
        if t_type == sre_constants.LITERAL:
            return z3.Re(chr(t_args))
        if t_type == sre_constants.RANGE:
            lo, hi = t_args
            return z3.Range(chr(lo), chr(hi))
        if t_type == sre_constants.IN:
            subpatterns = []
            for st_type, st_args in t_args:
                subpatterns.append(cls._parse_token(st_type, st_args))
            return z3.Union(*subpatterns)
        if t_type == sre_constants.CATEGORY:
            if t_args == sre_constants.CATEGORY_DIGIT:
                return z3.Range('0', '9')
            if t_args == sre_constants.CATEGORY_WORD:
                return z3.Union(
                    z3.Range('a', 'z'),
                    z3.Range('A', 'Z'),
                )
            if t_args == sre_constants.CATEGORY_SPACE:
                return z3.Union(*(z3.Re(ch) for ch in string.whitespace))
        if t_type == sre_constants.ANY and t_args is None:
            return z3.Intersect(
                z3.Range(z3.Unit(z3.BitVecVal(0, 8)), z3.Unit(z3.BitVecVal(255, 8))),
                z3.Complement(z3.Re('\n')),
            )
        raise UnsupportedError('cannot interpret regexp')

    def fullmatch(self, string: ProxySort, ctx: 'Context') -> 'BoolSort':
        if not isinstance(string, registry.str):
            ctx.add_exception(TypeError, "expected string or bytes-like object")
        print(z3.InRe(string.expr, self.expr))
        return registry.bool(expr=z3.InRe(string.expr, self.expr))
