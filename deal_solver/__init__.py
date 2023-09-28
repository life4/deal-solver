"""z3-powered solver (theorem prover) for deal.

https://github.com/life4/deal
"""
from __future__ import annotations

from ._eval_contracts import Contract
from ._exceptions import ProveError, UnsupportedError
from ._theorem import Conclusion, Proof, Theorem


__version__ = '0.1.2'
__all__ = [
    'Theorem',
    'Conclusion',
    'Contract',
    'Proof',
    'UnsupportedError',
    'ProveError',
]
