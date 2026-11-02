# quotient-lang

quotient-lang is a Cubical TT language for the core logic of a quotient
blockchain. A transaction body declares the keys that it reads and the keys
that it writes. The checker proves that each step keeps to that footprint,
and so it derives that two independent transactions commute. Histories that
differ only in the order of independent transactions are one value. No
program that compiles can trap: an abort is the value `nothing`.

Status: S1 DONE. The code is the permit-lang 18deea2 kernel with R0 and
REFUSE_NOT_IN_DESIGN, and its sample domain. The quotient-lang types are a
plan: `docs/PLAN.md`. Next: S2 (section 12).

## When to reach for quotient-lang

| Use quotient-lang when | Use something else when |
|---|---|
| You write chain logic where each transaction must declare its read and write keys, and the checker must prove them (footprint-typed chain logic). | You write an EVM contract: use Solidity or another EVM language. quotient-lang has no EVM target. |
| You need a mempool whose merge does not depend on order: a finite set, merged by union. | You write a general application, a web service or a script. |
| You write rollup state transitions: a step from root `r` to root `r'` that can compose with the next step. | You need a consensus protocol (leader election, fork choice). quotient-lang states agreement as a fact about histories, not as a protocol. |
| You must know which transaction pairs depend on order (the MEV surface), as a report. | You need only a ledger of records with no state transitions: use a database. |

## Files

- `docs/PLAN.md`: the readings, the base names, the laws, the targets, the
  slices and the rulings.
- `design/DESIGN.md`: the request, the rulings, the rectification of the
  two designs, the D1 digest and the D2 text. It is verbatim. Do not edit
  it.
- `AGENTS.md`: how an agent works in this repo.
- `SPEC.md`: the specification (kit text until the close slice).
- `formers/FORMERS.md`: the type formers. `formers/tcc-wasm.md` gives their
  status on the tcc-wasm host.
- `probe/CAPABILITY.md`: the host probe.
- `docs/STATUS.md` and `docs/VALIDATION.md`: the status and the gate
  results.
- `docs/host/README.md`: how to build and test the host kit.

## Gate

```
make -j 2 check
```

## License

MIT OR Apache-2.0.
