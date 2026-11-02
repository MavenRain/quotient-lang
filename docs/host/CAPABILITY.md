# TinyCC Wasm host capability

This file holds host facts only. Put the facts of your domain in the
`probe/CAPABILITY.md` of your language. Paths are relative to the host
kit, or to the root of a generated language. The toolchain was recorded
on 2026-10-08 on AArch64 Darwin. The gate facts below describe quotient-lang S1.

## Toolchain

- TinyCC 0.9.28rc (AArch64 Darwin) builds `build/langc` with
  `-std=c99 -Wall -Werror` (`Makefile:6`). `PIN` has the exact version.
- `cc -Wall -Wextra -Wswitch-enum -Werror -fsyntax-only` checks the same
  sources (`make check-clang`, `Makefile:7`). Each switch on an enum names
  every case and has no default arm.
- `tcc -run gen/embed.c` turns `domain/domain.lang` into `build/domain.c`
  at build time (`Makefile:20`). The domain is part of the executable.
- The kit uses the C99 `uint64_t` type for `Nat`. Unsigned arithmetic in
  C wraps modulo 2^64, so the evaluator and the IR use explicit carry
  tests to find an overflow.
- `src/wasm.c` writes the Wasm binary format directly: the type,
  function, memory, global, export and code sections, with LEB128
  numbers. It needs no library. The gate validates each module with
  `wasm-validate` and `wasm-objdump -x`, and checks its no-trap forms with
  `build/notraptool`. Runtime rows return at S8.

## Values

- `Nat` is an unsigned 64-bit integer. The lexer refuses a literal larger
  than 18446744073709551615 (`test/parse/nat-range.lang`).
- `natAdd` gives `Option Nat`, with `none` on overflow. `natSub` stops at
  0. `natDiv` and `natMod` take a `NonZero Nat` divisor. The kernel has no
  `natMul` word. `docs/host/README.md` gives the no-trap rule.
- There is no text type. The lexer refuses `"` (`test/parse/string.lang`).
- On Wasm, each op is total; a value is one word.

## Overflow tests on Wasm

- `ADD_CARRY` is `a + b < a`, modulo 2^64 (`src/wasm.c:152`).
- `SUB` is `select(a - b, 0, a >= b)`.
- `test/ir/natops.lang` covers the edge value 18446744073709551615:
  `addOr 18446744073709551615 1` is 0 (`natAdd` gives `none`),
  `addOr 18446744073709551615 0` is 18446744073709551615, and
  `pickSecond 18446744073709551615 1` is 1. The S3 gate checks the IR text
  and validates the module. The `wasm runs` and differential rows come
  back at S8 (Q-S3-2 (b), `docs/PLAN.md` section 1).

## Limits

- The checker and the evaluator stop at a depth of 2000
  (`src/front/check.c:14`, `src/front/core.h:14`). The parser stops at a
  nesting of 1000 (`src/front/parser.c:36`). These limits keep the C
  stack bounded. `test/gate.sh` checks a nesting of 1100 parentheses.
- The evaluator has a fuel of 20000000 steps (`src/front/core.h:15`).
  A large loop count can reach `EVAL_FUEL` or the arena limit. The
  differential grid uses large values only for entries with no loop;
  its runtime row returns at S8.
- All memory of `langc` comes from one arena with a limit of 1 GiB
  (`src/main.c:13`). A run that reaches it stops with `OOM`.
  `langc eval test/ir/spine.lang foldOnes 4294967296` stops with `OOM`.
- The Wasm memory has a fixed size (`src/wasm.c:303`): minimum = maximum =
  the pages of the largest heap bound of an entry, at least 1 page. The
  allocator has no check (`src/wasm.c:256`). An entry with no static heap
  bound refuses (`REFUSE_LOWER`, `test/ir/spine.lang`).
- The Wasm writer stops at a statement nesting of 2000 (`src/wasm.c:29`).
  The IR printer stops at 4000 (`src/front/lower.c:16`).
- A loop over a list spine has a fuel of 2^63 steps
  (`src/front/lower.c:771`). A spine walk whose allocations exceed the
  static heap limit refuses during lowering.
- Source files are at most 1 MiB (`src/front/front.h:7`).

## Measured numbers

- At S3, `make check` validates 4 modules with `wasm-validate` and
  `build/notraptool`, and checks 7 bad modules. It executes no Wasm calls.
  The 16-call `wasm runs` row and the differential row return at S8.
- `langc --kit build examples/entries.lang -o OUT` writes a module of
  193 bytes for three entries.

## HOST-LIMIT reasons

The IR is first-order (`src/ir.h`). It has words, heap blocks, branches,
counted loops and bounded loops. It has no calls, no function values and
no stack of its own. Two programs need more than that. The lowering
refuses them with a HOST-LIMIT code. These are not defects.

- `REFUSE_RUNTIME_CLOSURE` (`src/front/lower.c:536`): a function value
  must exist at run time, for example as the result of a `fold`. The IR
  has no closures. `test/ir/closure.lang` is the gate case.
- `REFUSE_RUNTIME_TREE` (`src/front/lower.c:1055`): a `fold` walks a value
  of a family with two or more recursive fields, and the value exists
  only at run time. A loop walks one spine. A tree needs recursion or an
  explicit stack. `test/ir/tree.lang` is the gate case.
