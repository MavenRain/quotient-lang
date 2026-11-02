# AGENTS.md

How an agent works in quotient-lang. This file is true at S0 (the seed).
The final form comes at slice S15 (`docs/PLAN.md` section 9, A5).

## State at S0

- The code is the lang-template tcc-wasm kit (5265a2a): `langc` (C99,
  TinyCC) and its sample domain in `domain/`.
- The quotient-lang types, laws, refusals and targets are a plan only:
  `docs/PLAN.md` sections 2 to 10.
- The USER ruled Q-R1 to Q-R8 before S0 (`docs/PLAN.md` sections 1 and
  14). The first build slice is S1 (section 12).
- `design/DESIGN.md` is verbatim. Do not edit it. A design change is a
  new paste and an open item.

## Gate

```
make -j 2 check
```

For a log that you compare byte for byte, run `make check` without `-j`:
a parallel make changes the order of the build lines.

## Rules

- No run-time error: an abort is the value `nothing` (R0,
  `docs/PLAN.md` section 2).
- Type constructors: only the cell monad `Maybe` (with `Eff`, its Kleisli
  form on `State`) and its dual, the ledger residual (R1, section 3).
- Base names: only the names of section 4. Each one cites D1 or D2.
- Each body declares its footprint (`reads`, `writes`) as static key
  patterns. The checker proves the frame law (section 5).
- Tests are guest `.lang` files and C tools. Do not add a node, Python or
  shell harness.
- No em-dashes or en-dashes outside `design/DESIGN.md`. The gate fails on
  them.
- Repo text uses short sentences in the active voice.

## Where to start

Read `docs/PLAN.md` section 12 (slices) and section 14 (questions).
