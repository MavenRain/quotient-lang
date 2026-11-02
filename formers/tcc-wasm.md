# TinyCC Wasm realization

Paths below are relative to this host kit, or to the root of a generated
language. The template's `formers/FORMERS.md` gives the host-neutral laws.
`src/front/check.c` lines are rows of the builtin table. `src/front/lower.c`
lines are the lowering to the IR.

DONE means: `langc check` accepts the former, `langc eval` computes it,
and `langc build` lowers it to Wasm when its value is first-order at run
time. Types, universes and proof contents erase on Wasm. Each op is total; a value is one word.

| ID | Former | Status | Where | Evidence |
|---|---|---|---|---|
| F1 | Product | DONE | `src/front/check.c:156`, `src/front/lower.c:607`, `src/front/lower.c:1171` | `examples/formers.lang:3`, `examples/laws.lang:14` |
| F2 | Coproduct | DONE | `src/front/check.c:157`, `src/front/check.c:169`, `src/front/lower.c:1179` | `examples/formers.lang:8`, `examples/laws.lang:15` |
| F3 | Option | DONE | `src/front/check.c:161`, `src/front/check.c:170`, `src/front/lower.c:1181` | `examples/formers.lang:11`, `examples/formers.lang:12` |
| F4 | List | DONE | `src/front/check.c:162`, `src/front/lower.c:872` | `examples/formers.lang:13`, `examples/laws.lang:3`, `test/ir/spine.lang:8` |
| F5 | Monad pure/map/bind | DONE over Option, Sum E and List | `src/front/check.c:172`, `src/front/lower.c:1080`, `src/front/lower.c:1095`, `src/front/lower.c:887`, `src/front/lower.c:902` | `examples/monad.lang:4`, `examples/monad.lang:6`, `examples/monad.lang:8`, `examples/laws.lang:10`, `test/ir/spine.lang:10` |
| F6 | Algebra fold | DONE over Nat, List and domain families. HOST-LIMIT: a run-time tree | `src/front/check.c:176`, `src/front/lower.c:1129`, `src/front/lower.c:872`, `src/front/lower.c:1014`, `src/front/lower.c:1034` | `examples/algebra.lang:4`, `examples/algebra.lang:8`, `examples/algebra.lang:6`, `test/ir/spine.lang:19`, `test/ir/tree.lang:3` |
| F7 | Algebra unfold | DONE into List with a Nat step limit | `src/front/check.c:177`, `src/front/lower.c:960` | `examples/algebra.lang:10`, `examples/algebra.lang:11`, `test/ir/spine.lang:5` |
| F8 | Filter | DONE over Option and List | `src/front/check.c:175`, `src/front/lower.c:1106`, `src/front/lower.c:922` | `examples/monad.lang:12`, `test/ir/spine.lang:11` |
| F9 | Non-dependent Pi | DONE. HOST-LIMIT: a function value at run time | `src/front/check.c:3027`, `src/front/lower.c:1252`, `src/front/lower.c:536` | `examples/functions.lang:2`, `examples/functions.lang:4`, `examples/laws.lang:7`, `test/ir/closure.lang:3` |
| F10 | Dependent Pi | DONE over `Type 0` and over Nat | `src/front/check.c:3027`, `src/front/lower.c:1244` | `examples/functions.lang:8`, `examples/paths.lang:8` |
| F11 | Sigma | DONE | `src/front/check.c:163`, `src/front/check.c:167`, `src/front/lower.c:1172`, `src/front/lower.c:1175` | `examples/sigma.lang:3`, `examples/sigma.lang:5`, `examples/sigma.lang:6` |
| F12 | Eq refl/symm/trans | DONE: `refl` and `sym` are builtins; `trans` is a guest def by `hcomp`; a path erases on Wasm | `src/front/check.c:164`, `src/front/check.c:178`, `src/front/check.c:182`, `domain/domain.lang:21`, `src/front/lower.c:1246` | `examples/equality.lang:4`, `examples/equality.lang:5`, `test/check/bad-refl.lang:2` |
| F13 | Eq transport/cong | DONE: `transport` is a guest def by `transp`; `cong` is a builtin; `langc eval` reduces `transp`, and only a stuck `transp` gets to the lowering | `src/front/check.c:181`, `domain/domain.lang:8`, `src/front/check.c:179`, `src/front/lower.c:1168`, `src/front/lower.c:1246` | `examples/equality.lang:6` |
| F14 | Universes | DONE for Type 0 and Type 1, without cumulativity | `src/front/lower.c:1243` | `examples/universes.lang:4`, `test/check/universe.lang:1`, `test/check/universe-range.lang:1` |
| F15 | Generic indexed family | PARTIAL: only the domain file declares an indexed family | `domain/domain.lang:329` | `examples/bagorbit.lang:7`, `test/check/elim-motive-index.lang:1` |

F6: a fold over a family with one recursive field (for example `Stack`)
lowers to a loop over the spine. A constructor with two or more recursive
fields (for example `Tree`) needs a tree at run time. The lowering refuses
it with `REFUSE_RUNTIME_TREE` when the tree exists only at run time.
A fold over a closed tree works, because normalization folds it at
compile time.

F9: a lambda stays only as the direct function argument of an eliminator.
When a function value must exist at run time, the lowering refuses it
with `REFUSE_RUNTIME_CLOSURE`. Both refusals are HOST-LIMIT reasons, not
defects. `docs/CAPABILITY.md` gives the reasons.

F15: a domain family can take index parameters, for example
`family Lot (size : Nat)`. A constructor takes the indices first
(`makeLot 3 250 : Lot 3`). The checker keeps `Lot 3` and `Lot 4` apart.
A program cannot declare a family (rule R1). No test has a field type
that refers to an index. The index erases on Wasm.

The refusal mutants are in `test/check/`: R1 `data.lang`, R2 `axiom.lang`,
R3 `rec.lang`, R4 `core-name.lang`. `test/check/expect.txt` gives the code
for each mutant.
