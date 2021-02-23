"""Solver core for deal, powered by z3-solver.
"""
# app
from ._exceptions import UnsupportedError
from ._theorem import Conclusion, Theorem, Proof


__version__ = '0.1.0'
__all__ = ['Theorem', 'Conclusion', 'Proof', 'UnsupportedError']
