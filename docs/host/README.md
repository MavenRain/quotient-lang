# TinyCC Wasm host kit

This kit compiles a small typed language to a WebAssembly MVP module.
One C99 program, `build/langc`, holds the parser, the checker, the
evaluator, the lowering to a first-order IR and the Wasm writer.
TinyCC builds it.

## Files

These files make the language and its Wasm target:

- the front end: `src/front/`, `src/ir.h`, `src/target.h` and
  `src/main.c`
- the target files: `src/wasm.c` and its opcode list `src/wasmop.h`
- the domain and its embed tool: `domain/` and `gen/`
- the examples: `examples/`
- the tests: `test/parse/`, `test/check/`, `test/eval/`, `test/ir/`,
  `test/notrap/`, `test/review.sh`, `test/fronttool.c`,
  `test/pathtool.c` and `test/notraptool.c`
- the differential files: `test/grid.awk` and `test/run-wasm.mjs`. The
  gate runs them for every example and both scalar IR fixtures.
- the build and gate files: `Makefile`, `test/gate.sh` and `PIN`
- the host docs: `docs/host/README.md`, `docs/host/CAPABILITY.md` and
  `formers/tcc-wasm.md`

## Build

From the root of this repository:

```sh
make build
make check
make check-clang
```

`build` runs `tcc -run gen/embed.c` to copy `domain/domain.lang` into
`build/domain.c`. Then it builds `build/langc` with
`tcc -std=c99 -Wall -Werror`. The domain is part of the executable.
`check-clang` compiles the same sources with
`cc -std=c99 -Wall -Wextra -Wswitch-enum -Werror -fsyntax-only`.
`check` does both steps, then runs `test/gate.sh`.
The gate needs `wasm-validate`, `wasm-objdump`, `wat2wasm` and `node` on
the `PATH`.
`PIN` records the tool versions of the last GREEN gate.
The build and the gate need no network access.

## Source language

A program is a sequence of `def NAME : TYPE := TERM`. A line comment
starts with `--`. Lambdas are `fun (x : A) => t`. There is no text type.

In kit mode, names include types `Nat Flag Prod Sum Option List Path PathP I`, values
`flagYes flagNo pair first second inl inr either none some option nil cons
pure map bind fold unfold filter pack witness payload refl sym trans
transport cong`, Nat operations `natAdd natSub natDiv natMod natEq natLe`,
the divisor type `NonZero Nat` with `nonZero` and `nonZeroValue`, and the
Flag eliminator `flagIf b yes no`. `Type 0 : Type 1` is the universe
chain. `Sigma (x : A) B` and `(x : A) * B` are dependent pairs.
`FORMERS.md` gives the status of each former.

The compiler enforces these rules:

| Rule | Code | The compiler refuses |
|---|---|---|
| R1 | `REFUSE_DATA` | a `family` declaration in a program |
| R2 | `REFUSE_AXIOM` | an `axiom` declaration |
| R3 | `REFUSE_REC` | `def rec`, or a definition that refers to itself or to a later definition |
| R4 | `REFUSE_NAME` | a core name, a domain name, a reserved name or a repeated name as a new definition |
| R4 | `REFUSE_TIME` | a time word (`now`, `block`, `timestamp`, `time`, `clock`, `epoch`) as a name or a use; the message says to count operations (`len r`, an `OpPos`) |

## CLI

```sh
build/langc check PROG [--json]
build/langc eval PROG NAME [ARGS...]
build/langc ir PROG
build/langc abi PROG
build/langc build PROG -o OUT [--runtime]
```

- `check` prints `ok`, or refuses the program.
- `check PROG --json` prints one line of JSON for an accepted program,
  for example the line of `--kit check examples/incl-sound.lang --json`:
  `{"ok":true,"axioms":["nodeDigestInj","storeLeafInj","nodeNotEmpty"]}`.
  The `axioms` list gives each O3 row (a hash assumption of PLAN O3, with
  no body) that a program definition uses, directly or through other
  definitions. The list is in definition order, not in the order of the
  uses. Only the bodies of the definitions count: a name in the declared
  type of a definition is not a use. When no definition uses an O3 row,
  the list is empty. `--json` must come after `PROG`. A refused program
  gives the diagnostic on stderr and no JSON.
- `eval` prints the normal form of `NAME`. Each argument is a decimal
  number. An entry has no trap (see "No traps").
- `ir` prints the first-order IR. It has one `func` for each entry.
- `abi` prints the name of each entry, one for each line.
- `build` writes the Wasm module to `OUT`. On this target, `--runtime`
  gives the same bytes.

The exit status is 0 for success, 1 for a refused program and 2 for a
usage or IO error. A diagnostic on stderr has the form
`langc: CODE: DEF: message`.

## Entries

An entry is a top-level program definition whose declared type is `Nat`,
`Flag`, or a first-order function from `Nat` and `Flag` arguments to a
`Nat` or `Flag` result. `build` exports each entry by its name. Each
parameter and the result is an `i64`. Other definitions are not exported.

`Nat` is an unsigned 64-bit integer. `natAdd` gives an `Option Nat`:
`none` on an overflow past 2^64 - 1. `natSub` stops at 0. The divisor of
`natDiv` and `natMod` is a `NonZero Nat`. `Flag` is 0 or 1.

## Compilation

Compilation is partial evaluation. The compiler normalizes the body of
each entry with the parameters as free variables. Types and universes erase.
Proof contents erase. A lambda stays only as the direct function argument of
`fold`, `unfold`, `map`, `bind`, `filter`, `either` or `option`. The
lowering puts its body into a loop or a branch. The lowering refuses two
programs with a HOST-LIMIT code (see `docs/CAPABILITY.md`):

- `REFUSE_RUNTIME_CLOSURE`: a function value must exist at run time.
- `REFUSE_RUNTIME_TREE`: a fold walks a tree that exists only at run time.

## No traps

No entry can trap (R0, `docs/PLAN.md` section 2). Each op of the IR is
total, and a value is one word with no trap flag (N5). `natAdd` gives
`none` on an overflow (N1). The divisor of `natDiv` and `natMod` is a
`NonZero Nat`, so the checker refuses a literal 0 with `REFUSE_PARTIAL`.
`langc eval` and the Wasm module give the same value for each entry.

The Wasm writer emits no trap form (N4):

- No `unreachable`. A `SWITCH` on a constructor tag uses its last arm as
  the `br_table` default.
- No `memory.grow`. The memory minimum is equal to the maximum: the
  pages of the largest static heap bound of an entry (N3).
- Each `div_u` and `rem_u` has a guard on its divisor.

`test/notraptool.c` reads each built module and refuses each of these
forms. The differential row runs each case on the module and compares
the result with the `langc eval` result. A Wasm trap is a mismatch.

The lowering lowers a value one time in a block. The blocks in that
block use the same result, but the two arms of a branch do not share
results.

The evaluation fuel (`EVAL_FUEL`) is a host limit, not a trap (N5).

Decision record: permit-lang `docs/PLAN.md` section 1 (Q-S3-1 to Q-S3-3) and
section 2 (N1 to N5 and the S3 result); quotient-lang `docs/PLAN.md`
sections 2 and 14 (Q-S1-1).

## Wasm layout

- The module has one memory of a fixed size and one mutable `i64` global,
  the heap pointer. The size is the pages of the largest heap bound of an
  entry (at least 1 page). `langc` adds the words of each heap block on the
  longest path of an entry. When an entry makes heap blocks in a loop with a
  run-time count, its heap use has no static bound: `langc ir` and `langc
  build` refuse it with `REFUSE_LOWER` (`heap use has no static bound`). A
  bound larger than 1 GiB gets the same refusal.
- Function 0 is the internal allocator `alloc (bytes : i32) -> i64`. It
  increases the heap pointer. It does not check the size, because the
  memory holds the heap bound of each entry.
- Function 1 + K is entry K. Each entry first sets the heap pointer to 0,
  so each call starts with an empty heap.
- A `Flag` argument is true when it is not 0. The entry sets it to 1.
- A word is 8 bytes. A heap block holds the tag in word 0 and the word of
  field K in word 1 + K. Each op is total; a value is one word.
- A tag switch is nested blocks and `br_table`. The last arm is the
  default, so a tag out of range runs the last arm.

## Domain slot

`domain/domain.lang` holds the families and the operations of the domain.
Only this file can declare a `family` (rule R1). `domain/README.md` tells
how to replace the sample domain.

## Gate

`make check` prints these lines when it is GREEN (`test/gate.sh`, then
`test/review.sh`, `build/fronttool` and `build/pathtool`):

| Line | What the gate does |
|---|---|
| `examples: 33 checked, 0 failed` | `langc check` accepts each `examples/*.lang` file |
| `parse refusals: 16 checked` | each `test/parse` file fails with the code in `test/parse/expect.txt`; one file has 1100 nested parentheses |
| `check refusals: 158 checked` | each `test/check` file fails with the code in `test/check/expect.txt`; the `TYPE_REFL` message shows both normal forms |
| `kit-only refusals: 10 checked` | each `REFUSE_KIT` row refuses a kit item in guest mode only: `langc --kit check` accepts the file |
| `time hint: 1 checked` | a `REFUSE_TIME` refusal names the op-count form (`len r`, an `OpPos`) |
| `evals: 98 checked` | `langc eval` gives each result in `test/eval/expect.txt` |
| `builds: 1 checked` | `langc build examples/functions.lang` writes a module that `wasm-validate` accepts |
| `ir: 1 lowered` | `langc ir examples/functions.lang` gives one `func` line for each `abi` line |
| `ir refusals: 5 checked` | `langc --kit ir` refuses `test/ir/closure.lang`, `kmap.lang`, `tree.lang`, `spine.lang` and `hop.lang`, each with its code |
| `ir lowerings: 2 lowered` | the `langc --kit ir` text of `test/ir/natops.lang` and `test/ir/block.lang` is `test/ir/natops.ir` and `test/ir/block.ir` |
| `notrap modules: 4 checked` | `langc build` writes the modules of `test/ir/natops.lang`, `test/ir/block.lang` and `examples/state-no-history.lang`, and `wasm-validate` accepts each one. `build/notraptool` (`test/notraptool.c`) accepts these three modules and the module of `examples/functions.lang`: no `unreachable`, no `memory.grow`, only the opcodes of `src/wasmop.h`, a divisor guard before each `i64.div_u` and `i64.rem_u`, and memory 0 with maximum = minimum. `build` lowers the `state` family of `examples/state-no-history.lang` as a plain family (Q-S3-3 (b)) |
| `notrap bad rows: 7 checked` | `build/notraptool` refuses each module of `test/notrap/bad/` (`wat2wasm` makes it from its `.wat` file): exit 1 and the message of its line in `test/notrap/bad/expect.txt`. The 7 modules have `unreachable`, `memory.grow`, an `i64.div_u` and an `i64.rem_u` with no guard, a memory maximum above the minimum, a memory with no maximum, and `i32.add` (an opcode that is not in `src/wasmop.h`) |
| `spine evals: 10 checked` | `langc --kit eval` gives each eval of `test/ir/spine.lang` at 4 |
| `wasm: 35 modules valid` | every example and both scalar IR fixtures build and pass `wasm-validate` |
| `differential: 2293 cases, 0 mismatches` | node runs each scalar export on the grid from `test/grid.awk`; each result equals `langc eval` |
| `gate: 0 failures` | the sum of all failures of `test/gate.sh` |
| `review regressions: passed` | `test/review.sh` passes |
| `domain regressions: passed` | `build/fronttool` (the domain declaration rows) passes |
| `path regressions: passed` | `build/pathtool` (the path rows) passes |

The gate also checks the usage and IO exit codes, five `eval` refusals and
the absence of em-dashes and en-dashes outside `design/DESIGN.md`. It
checks memory 0 of the modules of `test/ir/natops.lang` and
`examples/functions.lang` (0 heap words): 1 page, minimum = maximum.
`langc eval` refuses a Flag of 2 with `EVAL_ARGS` (`pick 2 4 9`). The
message of `test/check/sig-asset-higher.lang` must say "Asset: the slot
Asset must be first-order data". The doc check of lang-template (`perl
bin/doc-check.pl` with this repository as the root) must report 0
problems.

The differential grid includes the arithmetic entries of
`test/ir/natops.lang`, the block fold and every example. It tests zero
divisors, addition overflow and the u64 boundary. The gate also checks
that the Wasm boundary maps a Flag word of 2 to true (`flagPick 2 4 9`
gives 4). `langc eval` still refuses that argument with `EVAL_ARGS`.

## Known limits

- A `fold` over a bare `nil` cannot infer its type (`TYPE_INFER`). Use a
  definition with a declared `List` type.
- With no expected type, `either`, `map` and `cong` take the result type
  of the function at a fresh variable. A dependent result needs a
  declared type.
- A definition with a `List`, `Prod` or other non-scalar result is not an
  entry. `ir` and `abi` skip it.
- `langc eval` stops after 20000000 steps (`EVAL_FUEL`). The Wasm module
  has no step limit, so a large loop count can run on Wasm and stop in
  `eval`. The grid of `test/grid.awk` uses large values only for
  entries with no loop.
- The arena of `langc` stops at 1 GiB. The Wasm memory has a fixed size:
  minimum = maximum = the pages of the largest heap bound of an entry, at
  least 1 page. An entry with no static heap bound refuses
  (`REFUSE_LOWER`, `test/ir/spine.lang`).
- Source files are at most 1 MiB. `Nat` literals are at most
  18446744073709551615.
