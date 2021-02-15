from typing import Iterator
import z3


class Goal(z3.Goal):
    def __iter__(self) -> Iterator[z3.BoolRef]:
        for i in range(len(self)):
            yield self[i]
