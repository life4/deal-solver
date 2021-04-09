# stdlib
import typing

# external
import z3


class Model:
    _model: z3.ModelRef

    def __init__(self, model: z3.ModelRef) -> None:
        self._model = model

    def __iter__(self) -> typing.Iterator[typing.Tuple[str, object]]:
        for decl in self._model.decls():
            name = decl.name()
            z3_val = self._model[decl]
            if isinstance(z3_val, z3.FuncInterp):
                continue
            py_val = eval(repr(z3_val))
            yield name, py_val

    def __bool__(self) -> bool:
        return len(self._model) != 0

    def __str__(self) -> str:
        return ', '.join(f'{k}={v!r}' for k, v in sorted(self))

    def __repr__(self) -> str:
        return f'{type(self).__name__}({repr(self._model)})'
