# external
import z3

# app
from .._exceptions import UnsupportedError
from ._funcs import unwrap
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class StrSort(ProxySort):
    type_name = 'str'

    def _ensure(self, item, seq=False):
        pass

    @property
    def as_int(self):
        assert self.expr is not None
        int_proxy = registry['int']
        return int_proxy(expr=z3.StrToInt(self.expr))

    @property
    def as_str(self):
        return self

    @property
    def as_float(self):
        assert self.expr is not None
        float_proxy = registry['float']
        if z3.is_string_value(self.expr):
            val = float(self.expr.as_string())
            return float_proxy.val(val)
        raise UnsupportedError('cannot convert str to float')

    @property
    def as_bool(self):
        assert self.expr is not None
        return self.expr != z3.Empty(z3.StringSort())

    def contains(self, item):
        assert self.expr is not None
        self._ensure(item)
        return z3.Contains(self.expr, unwrap(item))

    def startswith(self, prefix):
        assert self.expr is not None
        return z3.PrefixOf(unwrap(prefix), self.expr)

    def endswith(self, suffix):
        assert self.expr is not None
        return z3.SuffixOf(unwrap(suffix), self.expr)

    def index(self, other, start=None):
        assert self.expr is not None
        int_proxy = registry['int']
        if start is None:
            start = z3.IntVal(0)
        return int_proxy(expr=z3.IndexOf(self.expr, unwrap(other), unwrap(start)))

    @property
    def length(self) -> z3.ArithRef:
        assert self.expr is not None
        int_proxy = registry['int']
        return int_proxy(expr=z3.Length(self.expr))
