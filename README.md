# deal-solver

[z3](https://github.com/Z3Prover/z3)-powered solver (theorem prover) for [deal](https://github.com/life4/deal).

```bash
python3 -m pip install deal-solver
```

## CLI

For CLI usage, see the [deal documentation](https://deal.readthedocs.io/). The solver doesn't provide a CLI on its own.

## API

Deal-solver is created specifically for deal. So, if you want to use it with another tool, you have to mimic deal. It's not hard, though. See `TestTheorem` implementation in [tests/helpers.py](./tests/helpers.py).

## The project state

This is an experimental project. it supports only limited subset of syntax an types. Still, it works for some simple cases. So, give it a try, it is free.
