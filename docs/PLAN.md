# quotient-lang plan

quotient-lang is a Cubical TT language for one job: the core logic of a
quotient blockchain. A transaction body declares the keys that it reads and
the keys that it writes. The checker proves that the step of the body keeps
to that footprint. From that proof it derives that two independent
transactions commute. So the language identifies histories that differ only
in the order of independent transactions, by construction. The mempool is a
finite set, merged by union. The ledger is the quotient of the history that
no later observer can tell apart. No program can trap: an abort is the value
`nothing`.

The design is `design/DESIGN.md`: the request, verbatim, the S0 rulings,
verbatim, the rectification of the two designs (D1 and D2) with the USER
rulings, the D1 digest, the D2 text, verbatim, and the overlap facts. This
file gives the readings of that request, the route, the slices and the open
items. The USER ruled Q-R1 to Q-R8 before S0 (section 14). So sections 2 to
5 are RULED, not proposals.

Status: S6 DONE (2026-11-06): `Trace` over `Body`, the generated `ind`,
`commute` and `D`, `[[ ]]` (`traceEval`), `Blockchain`, the sugar `<|`,
`++`, `[t]` and `[[t]]`, REFUSE_EQ_UNDECIDABLE, L4 and L9. S5
(2026-11-04) gave footprint families, key spaces, `step`, the `ind`
verb, the REFUSE_FOOTPRINT codes and L3. S4 (2026-11-03) gave the
slots `Body`, `Witness`, `Digest`
and `Sig`, the auth, agg and QC preludes (section 4),
REFUSE_WITNESS_READ, REFUSE_BAG_NONCOMM at `Bag Sig` (section 7) and
L5 (section 6). S3 (2026-11-03) gave `Pfin`, `in`, `union`, the slot
`Key`, `Footprint = Pfin Key`, REFUSE_BAG_NONCOMM at `Pfin` and L2. S2
(2026-11-02) gave `Amount`, `Bag`, `Value`, `Balance`, `[[ ]]v`,
`Delta`, `neg`, `Balanced`, REFUSE_OVERFLOW and REFUSE_BAG_NONCOMM at
`Bag`, with L1 and L8, on the S1 kernel (section 8.1). Next: S7
(section 12).

## 1. Rulings

| Date | Ruling | Source |
|---|---|---|
| 2026-11-02 | Targets: "Wasm STF + C node (Recommended)" (T1), "ZK circuit IR (rollup)" (T2), "JSON law report" (T3). Not chosen: "EVM bytecode". | DESIGN.md 2 |
| 2026-11-02 | Crypto: "Abstract + v1 binds (Recommended)". The language has one opaque `Digest` and one commutative `Sig`, with their laws. Binding stays a named assumption (O1). v1 binds SHA-256 and BLS12-381 in the C node only. | DESIGN.md 2 |
| 2026-11-02 | Grok design: "I will paste it". The USER pasted D2 (DESIGN.md 5). R2 is built from D1 and D2 at once (DESIGN.md 3). | DESIGN.md 2, 5 |
| 2026-11-02 | Name: "quotient-lang (Recommended)". Private repo MavenRain/quotient-lang, seeded from lang-template. | DESIGN.md 2 |
| 2026-11-02 | Host: TinyCC. All of `langc` is C99 that TinyCC builds, `langc mcp` too. The T1 node is C99 that TinyCC builds. From the request, not asked. | DESIGN.md 1 |
| 2026-11-02 | Q-R1 R1 reading: (a) accept. One cell monad and its dual; the HITs are R2 base types at fixed instances (section 3). | USER, pre-S0 |
| 2026-11-02 | Q-R2 Rectification verdicts X1 to X21: (a) accept as written (section 4). | USER, pre-S0 |
| 2026-11-02 | Q-R3 Numbers: (a) bounded u64 amounts; arithmetic is typed as `Maybe`; overflow is the abort value, never a trap (section 2). | USER, pre-S0 |
| 2026-11-02 | Q-R4 Canonical append: (a) `c ++ [t]` only; `langc fmt` rewrites any append sugar (A1). | USER, pre-S0 |
| 2026-11-02 | Q-R5 Footprint form: (a) static key patterns per body type, so `Ind` is decidable at compile time (section 5). | USER, pre-S0 |
| 2026-11-02 | Q-R6 QC (X15): (a) in v1, as a type with `Pfin Node`. | USER, pre-S0 |
| 2026-11-02 | Q-R7 Policy normal forms (D1 sec 12): (a) a later slice. | USER, pre-S0 |
| 2026-11-02 | Q-R8 Seed kit: (a) tcc-wasm (Wasm STF, C node, `langc mcp`); the ZK circuit IR is a later slice that ports the zkml-lang Circuit IR. | USER, pre-S0 |

The USER words for Q-R1 to Q-R8 (2026-11-02, verbatim): "Take the
recommendation for Q-R1 through Q-R8, and give next session prompt".

## 2. The reading of R0: no trap (RULED)

R0: no program that compiles can reach a run-time error, on any target.

The reading is the permit-lang and relay-lang reading: each operation is
total on its declared type, and each run of each target gives a value of
the result type. An abort is a value, never a trap. The step type is
`Eff = State -> Maybe State` (D1 sec 7, X5), and `nothing` is the abort.

| Rule | Statement | Where |
|---|---|---|
| N1 | Each operation is total on its declared type. An operation that can fail returns `Maybe`; `nothing` is the abort. | kernel, `REFUSE_PARTIAL` |
| N2 | Amounts are u64 (Q-R3 (a)). `add`, `sub` and `mul` on `Amount` return `Maybe Amount`. Overflow and underflow give `nothing`. `Delta` subtraction is total: it has no underflow (X13). | S2 |
| N3 | A step aborts only from the values that it read (the frame law, section 5). An aborted step leaves the state as it was: `step b s = nothing` and the run keeps `s`. | S5 |
| N4 | Recursion is structural only: the eliminators of the base types. There is no general fixpoint. | kernel, `REFUSE_PARTIAL` |
| N5 | The Wasm writer emits no `unreachable` and no trap form, and uses static memory only. `test/notraptool.c` checks each built module (relay-lang 5c386bb, permit-lang S3). | S1, S9 |
| N6 | The C node never gives an error to a program. Bytes that it cannot decode, a bad witness and a bad signature are values: `rejected malformed`, `rejected badWitness`, `rejected badSig`. | S10 |
| N7 | No equality test on `Eff` or on `Blockchain`. Equality of two effects over an infinite `State` is not decidable (X6). The checker refuses the test. S6 DONE: a two-argument test on `Eff` or on `Blockchain` gives `REFUSE_EQ_UNDECIDABLE`, also through an alias (Q-S6-6 (a)); eq-eff.lang, eq-eff-alias.lang, eq-chain.lang. | S6 |

Refusals at run time are values. Refusals at check time are `REFUSE_*`
codes (section 7).

## 3. The reading of R1: one cell monad and its dual (RULED, Q-R1 (a))

R1: the only type constructors and higher-kinded types are cell monads and
their duals, as Cubical TT realizes them.

- The cell monad is `Maybe` (partiality). The step type
  `Eff = State -> Maybe State` is the Kleisli form of `Maybe` on `State`.
  `Eff` is a monoid: `(f ; g) s = f s >>= g`, unit `just` (D1 sec 7, X5).
- Its dual is the ledger residual `Ledger -> (Trace -> Query -> Answer)`
  (D1 sec 9, X8): a behaviour that answers each query after each further
  history. It is a cofree-comonad behaviour (the Nerode quotient). A node
  holds a `Ledger`, and `query` reads the residual.
- The HITs of the designs enter as R2 BASE types at fixed instances:
  `Value = Bag Asset`, `Sigs = Bag Sig`, `Mempool = Pfin AuthTx`,
  `Footprint = Pfin Key`, `Signers = Pfin Node`, `History = Trace Body`,
  `Net = Delta Value`, `UTxO = FinMap OutRef Output`,
  `Store = FinMap Key Val`, and the truncations `Authorized b`, `QC b`,
  `Valid r r'` and `t <= u`. A program cannot apply `Bag`, `Pfin`,
  `Trace`, `Delta`, `FinMap` or a truncation to a new type.
- The kernel `REFUSE_CELL` refuses any other type constructor in a program.

## 4. The base signature (R2, RULED: Q-R2 (a))

Source: `design/DESIGN.md` section 3 (the rectification). Each admitted name
cites D1 (the digest, DESIGN.md 4) or D2 (the text, DESIGN.md 5), or both.
KEEP: both designs agree, or the name is D1 only and inside R0 and R1.
CORRECT: one design fixes the other; the fixed form wins. DROP: the name
conflicts with R0 or R1, or has no definition. A DROP row is a refused
name: a program that uses it gets a refusal (section 7).

| # | Admitted name(s) | D1 | D2 | Verdict | Slice |
|---|---|---|---|---|---|
| X1 | `Body`, `Witness`, `Authorized b`, `AuthTx` | sec 4 | Semantic domain (Tx) | CORRECT: D2 Tx is `Body` with a truncated witness; txid and effect read `Body` only. S4 DONE: the slots `Body` and `Witness`, `witnessOk`, `Authorized b` and `AuthTx` (auth prelude, Q-S4-1 (a)); `txid : Body -> Digest` (Q-S4-2 (a)) | S4 |
| X2 | `Ind a b` (Bernstein) | sec 7 | Semantic domain (t1 perp t2) | CORRECT: shared reads are allowed; D2 "etc." is not a definition | S5 |
| X3 | `Trace` (`eps`, `<|`, `swap` on `Ind`, trunc) | sec 8 | CTT realisation (generators) | KEEP: the only generator is commutation. S6 DONE: front.c generates `Trace` over `Body` with `traceEps`, `traceCons`, `traceSwap` on a pair with `ind a b` = `flagYes`, `traceSquash` and `traceFold`; `ind : Body -> Body -> Flag` comes from the Ind matrix (Q-S6-10 (a), Q-S6-11 (a)); `commute` for each pair of `Body` constructors gives the kernel path from `effSeq (step a) (step b)` to `effSeq (step b) (step a)` (Q-S6-3 (b), Q-S6-8 (a)); examples/trace.lang, examples/commute.lang | S6 |
| X4 | (absorption path) | sec 6 note | CTT realisation ("absorption of invalid or no-op transactions") | DROP, refused: "invalid" depends on the state, so it is no path on histories; replay counts. S6 DONE: `REFUSE_NOT_IN_DESIGN` (the S1 code; design-x4.lang) | S6 |
| X5 | `eval` = `[[ ]] : Trace -> Eff`, `Eff`, `;`, `just` | secs 7, 8 | Semantic domain (eval); Operations (eval factors) | KEEP: `nothing` is the abort value. S6 DONE: `traceEval` is `traceFold` into `Eff` (unit `just`, op `effSeq`, the swap case `commute`), after the set lemmas for `Eff` and `Trace` (Q-S6-26 (a), Q-S6-28 (a)); examples/eval.lang | S5, S6 |
| X6 | `Blockchain = Im [[ ]]` | secs 9, 13 | Semantic domain (List Tx / ~) | CORRECT: `List Tx / ~` = `Im eval`, built by image factorization with no decision procedure; a function out of `Blockchain` factors through `eval`. S6 DONE: `Blockchain` is the Sigma of `f : Eff` and the truncated fiber of `traceEval` over `f`, with `chainOf`, `chainEval` (the first projection) and `chainAppend` (Q-S6-4 (a)); examples/chain.lang | S6 |
| X7 | `++`, `[t]` (monoid on `Trace` and `Blockchain`) | sec 8 | Operations | KEEP: one spelling for append, `c ++ [t]` (Q-R4 (a)). S6 DONE: `traceAppend`, `traceOne` and the parser sugar: `a <| t` is `traceCons`, `c ++ d` is the append of the type of `c`, `[t]` is `traceOne` and `[[t]]` is `traceEval` (Q-S6-5 (a), Q-S6-9 (a)); examples/sugar.lang, 10 parse refusals | S6 |
| X8 | `Ledger = Trace / ~N`, `apply`, `query`, `[[ ]]N` | sec 9 | (none) | KEEP: node state; a right congruence is enough | S7 |
| X9 | `<=` (prefix), `Compatible` | sec 10 | Consensus ("agreement = path equality") | CORRECT: agreement is `Compatible` (a common extension); decidable on `Trace` through the Foata normal form | S7 |
| X10 | (`GenConsensus`, `CanonicalChain`, run colimit) | sec 10 | Consensus (CanonicalChain) | DROP, refused: no finite value; `Forks` and `~cons` have no definition. SPEC text only. S6 DONE: `REFUSE_NOT_IN_DESIGN` (the S1 code; canonical-chain.lang) | S6 |
| X11 | `Bag A` (comm, trunc), `Value = Bag Asset`, `Balance`, `[[ ]]v` | sec 2 | Consensus (List Output / perm) | KEEP: the free commutative monoid | S2 |
| X12 | `UTxO = FinMap OutRef Output` | secs 2, 12 | Consensus (List Output / perm) | CORRECT: outputs have unique refs, so a finite map, not a bag | S8 |
| X13 | `Delta M`, `neg`, `Balanced`, mint and burn policy | sec 3 | (none) | KEEP: subtraction is total | S2 |
| X14 | `agg : Bag Sig -> Sig` (commutative `Sig`) | sec 5 | (none) | KEEP: a non-commutative scheme is refused at `Bag Sig`. S4 DONE: the slot `Sig` and its six program names; the agg prelude gives `agg` (`bagFold`) and `aggOp`; no `sigComm`, or a wrong one, gives `REFUSE_BAG_NONCOMM` (Q-S4-4 (a)) | S4 |
| X15 | `QC b` (signer set outside, signatures inside the truncation) | sec 4 | (none) | KEEP, v1 (Q-R6 (a)). S4 DONE: the QC prelude; the program bit `quorum : Pfin Node -> bit` is in the `Sigma`, outside the truncation (Q-S4-5 (a)) | S4 |
| X16 | `Pfin A`, `in`, `union`, `Mempool = Pfin AuthTx` | sec 6 | (none) | KEEP: gossip merge is union. S3 DONE: `Pfin A`, `in` and `union`. `Mempool` moves to S4, because it needs `AuthTx` (S4). S4 DONE: `Mempool = Pfin AuthTx` in the auth prelude | S3, S4 |
| X17 | `reads`, `writes : Body -> Pfin Key`; frame law gives commute | sec 7 | (none) | KEEP: the core checker feature (section 5) | S5 |
| X18 | `FinMap Key Val`, `canon`, `root`, inclusion proof, `Digest` | sec 12 | (none) | KEEP: binding is assumption O1; policy normal forms later (Q-R7 (a)) | S8 |
| X19 | `Valid r r'`, `compose` | sec 13 | (none) | KEEP: the T2 circuit emits `Valid`; `compose` uses L4 and O1 once | S8, S17 |
| X20 | shards: `Trace (B1 + B2) ~ Trace B1 x Trace B2` | sec 11 | (none) | KEEP as a T3 report fact (cross-shard letter count), no type | S11 |
| X21 | `D = (Body x Body) minus Ind`, the MEV surface | sec 14 | Summary | KEEP: T3 lists the `D` pairs. S6 DONE: front.c generates `D : Body -> Body -> Flag`, the negation of `ind` (Q-S6-7 (a)); T3 is S11 | S6, S11 |

Design parameters that the rows use, each a base sort with decidable
equality and no other operation unless a row gives one: `Asset`, `Owner`,
`Key`, `Val`, `Node`, `OutRef`, `Output`, `Query`, `Answer`, `Amount`
(u64, Q-R3 (a)). `State` is `Key -> Val` (D1 sec 7), held as
`FinMap Key Val`.

`Pfin A` (S3) is the `Bag` generator form with the idempotence cell
`pfinIdem` (the union of `s` with `s` is `s`, Q-S1-5 (a)). `union` is
its operation. `in` is a prelude fold out of `Pfin A` into the bit
`Sum Unit Unit` by `or`, with an equality from the program (Q-S3-1 (b),
Q-S3-3 (a)). `Key` (S3, Q-S3-2 (a)) is a program slot, as `Asset` is,
and it must be first-order data (`REFUSE_SIG`, section 7). After the
program definition of `Key`, the front end splices the key prelude
`Footprint = Pfin Key` (`key_after_key` in `front_load` and
`front_load_domain`, src/front/front.c). A program that uses
`Footprint` and does not define `Key` gets NAME_UNKNOWN
(footprint-no-key.lang). `reads`, `writes` and the key patterns stay at
S5. `Mempool = Pfin AuthTx` moves to S4 (X16).

S4 (Q-S4-1 to Q-S4-8 (a)) adds four program slots: `Body`, `Witness`,
`Digest` and `Sig`. `Node` was a slot before S4. The slots `Body`,
`Witness` and `Digest` must be first-order data (`REFUSE_SIG`, section
7). The `Body` slot must not mention `Witness`, `Authorized` or
`AuthTx` (`REFUSE_WITNESS_READ`, Q-S4-2 (a)). `Digest` is abstract, and
O3 stays a named assumption (Q-S4-3 (a)). The kernel fixes the type of
these program names, with one `SIG_PROGRAM` row each (Q-S4-6 (a)):
`witnessOk : Body -> Witness -> bit`, `txid : Body -> Digest`, the six
monoid names of `Sig` (`sigIsSet`, `sigOne`, `sigMul`, `sigAssoc`,
`sigComm`, `sigUnitL`), `nodeEq`, `quorum : Pfin Node -> bit` and
`signs`. Here `bit` is `Sum Unit Unit`. A wrong type gives
`REFUSE_SIG`, with two exceptions: a `txid` type that mentions
`Witness` or `AuthTx` gives `REFUSE_WITNESS_READ`, and a wrong `sigComm`
gives `REFUSE_BAG_NONCOMM` (section 7). The front end
(src/front/front.c) splices three preludes:

- auth (`auth_after_witness`): `Authorized b`, the truncation of the
  witnesses `w` with `witnessOk b w = btrue` (Q-S4-1 (a)), `AuthTx`,
  `Mempool = Pfin AuthTx` (X16) and the L5 lemma `authTxEq`: two
  `AuthTx` values with equal bodies are equal (Q-S4-7 (a)). Example:
  examples/authtx.lang.
- agg: `agg : Bag Sig -> Sig` by `bagFold`, and `aggOp` (Q-S4-4 (a)).
  A program with the slot `Sig` and no `sigComm` gets
  `REFUSE_BAG_NONCOMM`. Example: examples/agg.lang.
  The six monoid names admit any set with the required proofs, including
  quotient sets. examples/agg-bag.lang checks `Sig = Bag Unit`, the empty
  and singleton aggregation rules, and `aggOp`.

- QC (`qc_after_signs`, the source `qc_source`): in `QC b`, the signer
  set and the bit `quorum q` are outside the truncation, and the
  signatures are inside it (X15, Q-S4-5 (a)). The inner `Sigma` has the
  binder `h`. A program that uses `QC` and does not define the QC names
  gets NAME_UNKNOWN (qc-no-quorum.lang). Example: examples/qc.lang.

`Amount` (S2, Q-S2-2 (a)) is a nominal builtin type that a guest can
use. `amountAdd` and `amountSub` give `Maybe Amount`: `none` at
overflow and at underflow, never a trap. A numeral is an `Amount`
literal when the wanted type is `Amount`. `Maybe A` is `Option A`
(`domain/domain.lang`). An `amountAdd` or `amountSub` result where an
`Amount` is wanted gives REFUSE_OVERFLOW (section 7). `langc` does not
lower a Wasm entry with a `Maybe` result, so the Wasm entries of
`examples/amount.lang` give an `Amount` (`none` keeps the old value).

Value prelude (S2, Q-S2-3 (a), Q-S2-5 (a), Q-S2-6 (a)): after a
program defines the slot `Asset`, the front end puts kernel
declarations after it:

- `Value = Bag Asset`.
- `Balance = Asset -> Amount`, and `valueBal v a`, the code name of
  `[[ ]]v`: the count of `a` in `v`. The C builtin `valueCount` (eval
  only, as `len`) counts. It compares two assets with the conversion
  check of the evaluator. So the `Asset` slot must be first-order data
  (REFUSE_SIG, section 7).
- `balanceAdd`: `amountAdd` at each asset, so it gives `Maybe Amount`.
- The family `Delta`: the formal differences `deltaOf a b` of `Value`,
  the path `deltaEq` when `a + d = c + b`, and the squash
  `deltaSquash`. Then `deltaZero`; `deltaSub`, the code name of
  `a - b`; `neg`; `Balanced d`, a path from `d` to `deltaZero`.
- `deltaAdd`, the code name of `+` on `Delta`: a nested fold. Its path
  case uses `deltaExt`: two maps out of `Delta` into a set are equal
  when they agree at each `deltaOf a b`. The helpers are `valueSwap`,
  `deltaShift` and `deltaAddZero`.
- The L8 paths (section 6): `deltaSelf` (`a - a = 0`), `balancedNeg`
  and `balancedAdd`.

`Delta` is `Delta Value` only (the instance `Net` of section 3). A
program without an `Asset` slot gets no value prelude: `Value` is then
an unknown name (NAME_UNKNOWN, `test/check/value-no-asset.lang`).

## 5. Footprint checking (RULED: X17, Q-R5 (a))

This is the core checker feature. D1 sec 7 gives the law. D1 does not
mechanize the frame law; quotient-lang checks it for each program.

### 5.1 Declarations

Each body type declares `reads` and `writes` as static key patterns. A key
pattern is a key space name applied to body fields or to constants, for
example `utxo(b.input)` or `acct(b.from)`. A pattern cannot read the state.
So the footprint of a body value is a finite set of keys, computed from the
body alone (`reads, writes : Body -> Pfin Key`, X17).

### 5.2 The frame law

The checker proves three facts for each step:

1. The step reads only keys in `reads b`.
2. The step writes only keys in `writes b`.
3. The step aborts from the values that it read alone.

The canonical step has three phases: read (each `get` names a `reads`
pattern), decide (pure code over the body and the read values; `nothing`
only here), write (each `set` names a `writes` pattern). There is no `get`
after a `set`. A step in this form satisfies the frame law by its shape.
`langc fmt` prints this form (A1). Refusals: `REFUSE_FOOTPRINT_READ`,
`REFUSE_FOOTPRINT_WRITE`, `REFUSE_FOOTPRINT_PHASE` (section 7).

### 5.3 Ind and commute

`Ind a b` is the Bernstein condition (X2): `writes a` is disjoint from
`reads b` and `writes b`, and `writes b` is disjoint from `reads a`.
Shared reads are allowed. The frame law gives commute: if `Ind a b`, then
`step a ; step b = step b ; step a` (D1 sec 7). The checker discharges this
law for each body type pair (L3).

### 5.4 Decidability (Q-R5 (a))

For each pair of body types the checker computes one of three verdicts at
compile time:

- `ind`: no pattern of one type can unify with a conflicting pattern of the
  other (different key spaces, or different constants). The pair always
  commutes.
- `dep`: the patterns always overlap. The pair is in `D` (X21).
- `ind-if`: a finite list of field inequalities. On two body values the
  test is a finite comparison of keys, because `Key` has decidable
  equality.

T3 prints this matrix. The node uses it to put a trace in Foata normal
form (X9).

### 5.5 S1 survey (2026-11-02, committed trees only)

**1. Key-pattern syntax (proposal for S5).** The body type is a one-constructor `family` (permit-lang 18deea2 `parse_family`). Its fields are projections (`proj_app`, src/front/check.c 2472). The footprint clause follows the family, in the way that the `sealed` and `law` modifiers attach (src/front/parser.c 591 to 600).
```
keyspace  ::= 'keyspace' Space ':' Type '->' 'Key'
decl      ::= 'family' Name ':=' ctor 'footprint' Binder reads writes
reads     ::= 'reads' '[' pats ']'        writes ::= 'writes' '[' pats ']'
pats      ::= (pat (',' pat)*)?
pat       ::= Space '(' arg (',' arg)* ')'
arg       ::= Binder '.' Field | Nat | Name     -- Name: a closed def
item      ::= 'get' Name ':=' pat | 'let' Name ':=' term | 'set' pat ':=' term
```
Reused tokens: `[`, `,`, `]`, `:=`, `(`, `)`. New tokens: `.` (today an identifier char in internal mode only, src/front/lexer.c 135), and `keyspace`, `footprint`, `reads`, `writes`, `get`, `set`. A `get` or `set` names a pattern by its text. The checker compares it with the declared list after it renames the binder.

**2. Three-phase step.** The step body is one flat list of items. `get` and `set` are items, not terms, so a pure term cannot hold them. The checker makes one pass and keeps a phase: read, decide or write. The phase starts at read.
- `REFUSE_FOOTPRINT_READ`: the pattern of a `get` is not in `reads`.
- `REFUSE_FOOTPRINT_WRITE`: the pattern of a `set` is not in `writes`. A `set` moves the phase to write.
- `REFUSE_FOOTPRINT_PHASE`: a `get`, or a `let` that can give `nothing`, when the phase is write.
- `REFUSE_FOOTPRINT_DYNAMIC`: an `arg` that is not `b.field`, a numeral or a closed def. An example is a name bound by a `get`. The checker tests this at the declaration and at each `get` and `set`.

**3. The `Ind` matrix (C99 sketch).**
```c
typedef enum { ARG_FIELD, ARG_CONST } ArgKind;
typedef struct { ArgKind kind; uint32_t index; } PatArg;
typedef struct { uint32_t space; const PatArg *args; uint32_t arg_count; } KeyPat;
typedef struct { uint32_t family; const KeyPat *reads, *writes; uint32_t read_count, write_count; } Footprint;
typedef enum { IND_ALWAYS, IND_DEP, IND_IF } IndVerdict;          /* ind, dep, ind-if */
typedef enum { OPD_FIELD_A, OPD_FIELD_B, OPD_CONST } OpdKind;
typedef struct { OpdKind kind; uint32_t index; } Operand;         /* field, or constant pool index */
typedef struct { Operand left, right; } IndLit;                   /* left != right; not both OPD_CONST */
typedef struct { const IndLit *lits; uint32_t lit_count; } IndClause;   /* OR */
typedef struct { uint32_t a, b; IndVerdict verdict; const IndClause *clauses; uint32_t clause_count, dep_space; } IndRow; /* AND */
typedef struct { const IndRow *rows; uint32_t row_count, body_count; } IndMatrix;
```
There is one row for each unordered pair `a <= b` in declaration order, `a = b` included. The rows grow in an arena, as merge-lang `machine_row` does. Each conflict pair is a pattern pair from `writes a` x (`reads b` + `writes b`), or from `reads a` x `writes b`:
- Different spaces, or two different constants at one position: the pair does not conflict, so the checker skips it.
- Otherwise the checker makes one clause. The clause has one literal for each position that holds a field.
- An empty clause means `dep`.
- No clauses means `ind`. Some clauses means `ind-if`.

T3 (S11) prints one JSON row for each pair, as merge-lang `row_json` does. The node (S7, S10) looks up the row by the two body tags. It swaps the sides when the tag of `a` is larger. Then it tests each clause on the two body values with `Key` equality. Foata normal form uses this test.

**4. Sources to port**

| Repo | SHA | Path(s) | Take | Slice |
|---|---|---|---|---|
| merge-lang | 7bbcd58 | src/front/core.h 226 to 251 (`RowClass`, `RowMark`, `PairRow`) | the per-pair row shape | S5 |
| merge-lang | 7bbcd58 | src/front/check.c 3693 to 3700 (`OpWrites`), 4260 (`machine_row`), 4421 to 4470 (`pair_cover`, `form_row`) | per-op write flags, arena rows, pairs O1 <= O2, first-match class map | S5 |
| merge-lang | 7bbcd58 | src/front/json.c 116 (`CLASS_NAME`), 185 (`row_json`) | JSON pair rows | S11 |
| merge-lang | 7bbcd58 | domain/domain.lang (`orIdem`, `natMaxIdem`, comm, assoc) | semilattice law proofs, the model for L2 | S3 |
| quorum-lang | 4537d57 | examples/bag.lang 49 to 75 (`FMSet` generator form, `module Bag` union laws) | the HIT; `Pfin` = this plus an idempotence 1-cell | S2 (`Bag`), S3 |
| quorum-lang | 4537d57 | src/front/check.c 1711 to 1725 (`bag_shaped`), src/front/basenames.c 50, test/check/cell-fmset-cons.lang | CM shape check; `REFUSE_CELL` for the cons form | S3 |
| quorum-lang | 4537d57 | examples/agent/05-replica-merge.lang | join merge (comm, assoc, idem) | S3 (`Mempool` union) |
| permit-lang | 18deea2 (HEAD 505ca37) | src/front/parser.c 591 to 600, `parse_family`; src/front/check.c 2472 (`proj_app`); src/front/lexer.c 135 | modifier and family forms, projections | S5 |

Notes:
- merge-lang moved from ff5720b to 7bbcd58 (S8 agent kit, MCP). core.h did not change. check.c has 22 changed lines.
- The quorum surface uses an Agda-like Unicode syntax. The port must rewrite it into the permit-lang `family` syntax.
- Other repos: no checker. The committed trees of all ~/Documents/*-lang repos have no `footprint|bernstein|frame law|read set|write set|trace swap|foata` checker. This includes relay 9109e2a, cairn a56e602, orbit 2162fb2, tranche 9aafbf8 and accrue 20852a1. merge-lang 7bbcd58 is the best match: it has pair classes, but it writes flags for each part, not key patterns. charter-lang dff5802 docs/PLAN.md 373 (Q-S2d-1) has an independence relation over footprints for tests only. It has no checker.


## 6. Laws and assumptions

| Law | Statement | Discharge |
|---|---|---|
| L1 | `Bag` is commutative: an eliminator out of `Bag A` gives the `comm` clause. `agg (xs ++ ys) = agg xs (x) agg ys`. | kernel, per eliminator. S2 DONE at `Bag`: a fold or elim out of `Bag` with a wrong count of cases gives `REFUSE_BAG_NONCOMM` (Q-S2-4 (a)). S4 DONE at `Bag Sig`: the agg prelude gives `agg` and `aggOp`; a program with the slot `Sig` and no `sigComm`, or a wrong `sigComm`, gets `REFUSE_BAG_NONCOMM` (Q-S4-4 (a)); examples/agg.lang; `examples/bag.lang`. `agg` needs O2 (S4) |
| L2 | `Pfin` union laws: unit, assoc, comm, idem. Mempool merge is order-free. S4: `Mempool = Pfin AuthTx` (auth prelude), so these laws hold at `Mempool` (examples/authtx.lang). | prelude (merge-lang S1b, quorum-lang FMSet port), S3 DONE at `Pfin`: `unionUnitL`, `unionUnitR`, `unionAssoc`, `unionComm` and `unionIdem` (domain/domain.lang); `examples/pfin.lang`. The `Mempool` instance comes with `AuthTx` (S4) |
| L3 | Trace swap: if `Ind a b`, `[[a <| b <| t]] = [[b <| a <| t]]`. | checker, from the frame law (section 5). S5 DONE by shape (Q-S5-5 (a)): the read, decide, write phases of each `step` and the `Ind` matrix (`langc ind`) are the evidence; there is no kernel path term. |
| L4 | `[[t ++ u]] = [[t]] ; [[u]]`, and `[[ ]]` is the unique monoid map that extends `step` (D1 sec 8). | prelude. S6 DONE: `evalAppend` by a dependent `Trace` elim (Q-S6-27 (a)); examples/eval-append.lang |
| L5 | No-malleability: equal bodies give equal `AuthTx`; txid reads `Body` only. | checker: a step or txid that reads a `Witness` is refused. S4 DONE for `txid` and the `Body` slot: `REFUSE_WITNESS_READ` (Q-S4-2 (a)), and the prelude lemma `authTxEq` (Q-S4-7 (a)); examples/authtx.lang. S5 DONE for `step`: a footprint family that mentions `Witness`, `Authorized` or `AuthTx` gives `REFUSE_WITNESS_READ` (step-reads-witness.lang, step-reads-witness-alias.lang). |
| L6 | Nerode right congruence: `t ~N u` gives `t ++ k ~N u ++ k`. | prelude |
| L7 | `Valid` compose: `Valid r r'` and `Valid r' r''` give `Valid r r''`. Uses L4 and O1 once. | prelude; T2 emits it |
| L8 | `Delta`: `a - a = 0`; `Balanced` is closed under `+`. | prelude, S2 DONE: `deltaSelf` (`a - a = 0`), `balancedAdd` (Q-S2-6 (a)) and `balancedNeg` (section 4); `examples/value.lang` |
| L9 | `eval` factors through `Blockchain` (X6). | by construction. S6 DONE: `chainEval` of `chainOf t` is `traceEval t` by refl (Q-S6-4 (a)); examples/chain.lang |

Assumptions (named, never proved in the language):

- O1 Binding: `root` is injective on the quotient (D1 sec 12).
- O2 `Sig` is commutative: BLS12-381 aggregation (crypto ruling).
- O3 Hash collision resistance of `Digest` (v1: SHA-256 in the C node).

`langc check --json` counts each discharged law and lists O1 to O3 as
assumptions (A2).

## 7. Refusal names (proposals until their slice)

| Code | Refuses | Slice |
|---|---|---|
| `REFUSE_CELL` | A type constructor other than the cell monad and its dual (kernel) | S1 |
| `REFUSE_PARTIAL` | A partial operation or general recursion (kernel R0) | S1, DONE (port). Two sites give this code for a partial name in a spine head: `unknown_name` and `var_core`. A mutant that removes the `unknown_name` refusal is equivalent: `var_core` then refuses the same name with the same code and text. The S1 mutant PARTIAL-CODE changes the code at `unknown_name`, and the row partial-name.lang kills it. |
| `REFUSE_NOT_IN_DESIGN` | A name of the DROP rows X4 and X10 in any declaration form or binder (path 1); an axiom of a universe type whose name is not an admitted base sort (path 2, Q-S1-2 (a)) | S1, DONE |
| `REFUSE_SIG` | A program that does not keep to the base signature of section 4: a base sort that is not a slot of `Type 0`, a program definition of a kernel name of S2 to S8, or an `Asset` slot that is not first-order data (Q-S2-5 (a)) | S1 (port: the orbit-lang sample table). S2, DONE: the table is now the section 4 names (Q-S1-3 (a)). The 9 base sorts other than `Amount` are slots of `Type 0`, and the kernel names of S2 to S8 are defined rows. A mutant that makes the `SIG_DEFINED` case of `check_sig` give 1 is equivalent: `kernel_sig` refuses the same program first. The S2 mutant SLOT-FIRST-ORDER lived in round 1: the prelude `valueBal` then refuses the same program by `rule_value_count` with the same code. The message row of sig-asset-higher.lang ("Asset: the slot Asset must be first-order data") kills it. S3, DONE at `Key` (Q-S3-2 (a)): the `Key` slot must be first-order data. Row: sig-key-higher.lang, with a message row that names the slot `Key`. A mutant that removes the key splice from `front_load_domain` (KEY-SPLICE-2) is equivalent: `langc` has no caller of `front_load_domain`, and the guest mode and `--kit` both use `front_load` (Q-S3-6 (a)). S4, DONE (Q-S4-3, Q-S4-6 (a)): the slots `Witness` and `Digest` must be first-order data (witness-higher.lang, digest-higher.lang); a program definition of `Mempool` is refused (mempool-define.lang); a wrong type of a program name that the kernel fixes, for example `witnessOk` or `quorum`, is refused (witnessok-type.lang, qc-quorum-wrong.lang). S5, DONE: with a footprint family, a program def of `Body` gives `REFUSE_SIG` (Q-S5-8 (a); body-footprint.lang, body-footprint-before.lang). |
| `REFUSE_OVERFLOW` | `Amount` arithmetic used outside `Maybe` | S2, DONE: an `amountAdd` or `amountSub` result where an `Amount` is wanted (`overflow_result_ok`). Rows: amount-overflow.lang, amount-underflow.lang. |
| `REFUSE_BAG_NONCOMM` | An eliminator out of `Bag` or `Pfin` without its path clauses; a non-commutative `agg` (E5) | S2, DONE at `Bag` (Q-S2-4 (a)): a fold or elim out of `Bag` with a wrong count of cases. Rows: bag-no-squash.lang, bag-no-comm.lang, bag-elim-no-comm.lang. S3, DONE at `Pfin`: a fold or elim out of `Pfin` with a wrong count of cases (no `pfinIdem` case). Rows: pfin-no-idem.lang (the message names the `pfinIdem` case), pfin-elim-no-idem.lang. S4, DONE at `Bag Sig` (Q-S4-4 (a)): a program with the slot `Sig` and no `sigComm`, or a `sigComm` of a wrong type. Rows: sig-no-comm.lang, sig-comm-wrong.lang. |
| `REFUSE_WITNESS_READ` | A step or txid that reads a `Witness` (L5) | S4, DONE for `txid` and the `Body` slot (Q-S4-2 (a), by type): a `Body` slot that mentions `Witness`, also by an alias (body-has-witness.lang, body-alias-witness.lang), or a `txid` whose type mentions `Witness` or `AuthTx` (txid-reads-witness.lang, txid-authtx.lang). S5, DONE for `step` (S5 survey section 4): a footprint family that mentions `Witness`, `Authorized` or `AuthTx`, also by an alias (step-reads-witness.lang, step-reads-witness-alias.lang). |
| `REFUSE_FOOTPRINT_READ` | A `get` outside `reads` | S5, DONE: a `get` pattern that is not in the `reads` of the footprint (X17; footprint-read.lang) |
| `REFUSE_FOOTPRINT_WRITE` | A `set` outside `writes` | S5, DONE: a `set` pattern that is not in the `writes` of the footprint (X17; footprint-write.lang) |
| `REFUSE_FOOTPRINT_PHASE` | A `get` after a `set`, or `nothing` after a `set` | S5, DONE: the phase order is read, decide, write; a `let` at `Maybe T` after a `set` is also refused (X17, Q-S5-4 (a); footprint-phase-get.lang, footprint-phase-let.lang) |
| `REFUSE_FOOTPRINT_DYNAMIC` | A key pattern that reads the state (Q-R5 (a)) | S5, DONE: a footprint argument that is not `b.field`, a numeral or a closed def, or a step pattern argument that is a name of a `get` or a `let` (X17, Q-S5-21 (a); footprint-dynamic-*.lang, 6 rows) |
| `REFUSE_FOOTPRINT_SHAPE` | A footprint clause on a form that is not a family of one sort with one constructor, no parameters and no index (Q-S5-12 (a), Q-S5-17 (a)) | S5, DONE: footprint-shape-*.lang (5 rows) and footprint-param.lang |
| `REFUSE_KEYSPACE` | A key space that is not `A1 -> ... -> An -> Key` with n >= 1 and key argument types (Q-S5-13 (a), Q-S5-14 (a), Q-S5-25 (a)), or a footprint pattern with a wrong arity (Q-S5-16 (a)) | S5, DONE: keyspace-codomain.lang, keyspace-no-arg.lang, keyspace-arg-order.lang, keyspace-family-arg.lang, keyspace-alias-arg.lang, footprint-space-arity.lang |
| `REFUSE_STEP` | A second `step` for one family (Q-S5-20 (a)) | S5, DONE: step-twice.lang |
| `REFUSE_EQ_UNDECIDABLE` | An equality test on `Eff` or `Blockchain` (N7) | S6 |

## 8. Route

### 8.1 Kernel

S1 ports a Cubical TT kernel that has R0 (`REFUSE_PARTIAL`, the no-trap
Wasm writer, `test/notraptool.c`). Candidates: permit-lang (the relay-lang
05dd63b kernel plus R0 from relay-lang 5c386bb, at S3 of permit), and
relay-lang itself. The affine layer of permit-lang S4 is not needed. S1
surveys the candidates, records the SHA and the tree, and the cut list.

S1 result (2026-11-02, W/S1-survey.md): permit-lang 18deea2 "Port R0 and
the no-trap Wasm writer from relay-lang (S3)", tree fc4f8475. S1 took 230
of its 233 paths (185 A, 41 M, 2 D, 1 R100). It did not take the permit
text of docs/PLAN.md, AGENTS.md and README.md. Not taken: permit-lang
505ca37 (the S4 affine layer) and relay-lang 9109e2a (the relay domain).
The cut list (crypto, the ZK prelude, the chain words, the relay domain)
is at relay 05dd63b and permit S3. The kernel keeps REFUSE_TIME and the
other codes of 18deea2. S2 replaced the orbit-lang sample
signature of REFUSE_SIG with the section 4 names (Q-S1-3 (a)). S2 adds
`conv_system_same` to `src/front/eval.c` (Q-S2-7 (a), section 13 K7).

### 8.2 The three targets

- T1 (now): Wasm STF and C node. `langc` compiles each body type to a Wasm
  step function, with its footprint and the `Ind` matrix. A C node
  (`quotientd`, C99 that TinyCC builds) applies traces, merges the mempool
  by union, and answers queries. It binds SHA-256 and BLS12-381 (crypto
  ruling). S9 and S10.
- T2 (later, Q-R8 (a)): ZK circuit IR. Emit `Valid r r'` as a circuit, and
  `compose` as recursive aggregation. Port the zkml-lang Circuit IR
  (section 11). S17.
- T3: JSON law report: the footprints, the `Ind` matrix and `D` (the MEV
  surface), each law discharged, the assumptions O1 to O3, the
  cross-shard letter count (X20). `docs/REPORT-JSON.md`. S11.

## 9. Agent adoption (A1 to A6)

| Item | Request words | Plan |
|---|---|---|
| A1 | one canonical form per operation; `langc fmt` | `c ++ [t]` only (Q-R4 (a)); the three-phase step (5.2); S12 |
| A2 | `langc check --json`, fix hints, counts | counts: parsed, typed, laws discharged; each `REFUSE_*` has a fix hint; S13 |
| A3 | SKILL.md with 3 to 5 graded examples | G1 transfer, G2 UTxO spend, G3 mempool merge, G4 BLS quorum, G5 rollup `Valid`; S15 |
| A4 | `langc mcp` in TinyCC | stdio MCP server in C99; tools fmt, check, report; S14 |
| A5 | AGENTS.md and a README when-to-use table | this seed has both; the final form at S15 |
| A6 | token count against Python and Rust | the G1 to G5 programs in the three languages, one tokenizer; S16 |

## 10. Demo rows

| Row | Program | Expected |
|---|---|---|
| E1 | A UTxO pair with disjoint spends | The two orders are one `Trace` value: the path is `swap`, the check is `refl` on the Foata form |
| E2 | A double spend of one `OutRef` | The pair is in `D`; the order stays; the second step gives `nothing` |
| E3 | Two mempools merged | `m1 union m2 = m2 union m1` (L2) |
| E4 | Two `Valid` proofs in a row | `compose` gives one `Valid` (L7) |
| E5 | ECDSA signatures concatenated into a `Bag Sig` | Refused: `REFUSE_BAG_NONCOMM` |
| E6 | A witness encoded again | The txid does not change (L5) |

## 11. Port pins (2026-11-02, `git -C <repo> log -1`; S1 repin: merge-lang moved)

| Repo | HEAD | Use |
|---|---|---|
| lang-template | 5265a2a | the seed kit (tcc-wasm) |
| permit-lang | 505ca37 | kernel with R0 (S1 took 18deea2, tree fc4f8475), R0 and R1 table, A1 to A6 shape |
| relay-lang | 9109e2a | kernel and R0 source (S1 candidate) |
| quorum-lang | 4537d57 | `Pfin` (FMSet), CRDT merge, IVC compose |
| merge-lang | 7bbcd58 | semilattice merge laws (S1b induction port), Wasm merge engine (S7) |
| zkml-lang | 968dce4 | Circuit IR (T2) |
| zkpolicy-lang | 1d263fb | ZK verifier |
| leaf-lang | 5ccc494 | gate dash-check skip for design/DESIGN.md |

Some of these repos have work that is not committed. A port takes the
committed tree only. Each slice pins the SHA again at its survey.

## 12. Slices

One session for each slice: scope, gate, mutants, docs, close.

| Slice | Work | Status |
|---|---|---|
| S0 | Seed from tcc-wasm, DESIGN.md, this plan, README table, AGENTS.md; serial gate EXIT 0 (9 parse refusals, 19 check refusals, 32 evals, 10 lowered, 13 Wasm modules valid, 813 differential cases, 0 mismatches, review and domain regressions passed); seed commit; private repo | DONE |
| S1 | First build slice. Survey and port the Cubical TT kernel with R0 (8.1): `REFUSE_CELL`, `REFUSE_PARTIAL`, the no-trap Wasm writer, `test/notraptool.c`. Add `REFUSE_NOT_IN_DESIGN` with the section 4 name list. Survey the footprint checker (section 5): the key-pattern syntax, the three-phase step, the sources to port. | DONE: serial gate EXIT 0 (31 examples, 16 parse refusals, 160 check refusals, 10 kit-only refusals, 86 evals, 4 notrap modules, 7 notrap bad rows, 10 spine evals, 0 failures; review, domain and path regressions passed). Review restored 33 valid Wasm modules and 1088 differential cases with 0 mismatches; 7 of 8 mutants KILLED, PARTIAL equivalent (section 7) |
| S2 | `Amount` (u64, `Maybe` arithmetic), `Asset`, `Bag`, `Value`, `Balance`, `[[ ]]v`, `Delta`, `neg`, `Balanced`; `REFUSE_OVERFLOW`; L1, L8. | DONE: serial gate EXIT 0 (31 examples, 16 parse refusals, 154 check refusals, 10 kit-only refusals, 90 evals, 4 notrap modules, 7 notrap bad rows, 10 spine evals, 33 valid Wasm modules, 2293 differential cases with 0 mismatches, 0 failures; review, domain and path regressions passed). 20 of 20 mutants KILLED (SLOT-FIRST-ORDER by the message row sig-asset-higher.lang); the `SIG_DEFINED` mutant is equivalent (section 7) |
| S3 | `Pfin`, `in`, `union`, `Key`, `Footprint`; L2. | DONE: serial gate EXIT 0 (33 examples, 16 parse refusals, 158 check refusals, 10 kit-only refusals, 98 evals, 4 notrap modules, 7 notrap bad rows, 10 spine evals, 35 valid Wasm modules, 2293 differential cases with 0 mismatches, 0 failures; review, domain and path regressions passed). 11 of 12 mutants KILLED; KEY-SPLICE-2 is equivalent (section 7, Q-S3-6 (a)). `Mempool` moves to S4 (X16) |
| S4 | `Body`, `Witness`, `Authorized`, `AuthTx`, `Mempool = Pfin AuthTx`, `Digest` (abstract), `Sig`, `agg`, `QC`; `REFUSE_WITNESS_READ`, `REFUSE_BAG_NONCOMM` at `Bag Sig`; L5. | DONE: serial gate EXIT 0 (37 examples, 16 parse refusals, 171 check refusals, 10 kit-only refusals, 106 evals, 4 notrap modules, 7 notrap bad rows, 10 spine evals, 39 valid Wasm modules, 2293 differential cases with 0 mismatches, 0 failures; review, domain and path regressions passed). Mutants: 14 of 15 KILLED; AUTH-SPLICE-2 is EQUIVALENT (the S4 mutants table below). |
| S5 | `State`, `Eff`, `step`, `reads`, `writes`, the frame-law checker, `Ind`, the `Ind` matrix; `REFUSE_FOOTPRINT_*`; L3. | DONE: serial gate EXIT 0 (56 examples, 18 parse refusals, 215 check refusals, 10 kit-only refusals, 134 evals, 4 notrap modules, 7 notrap bad rows, 10 spine evals, 58 valid Wasm modules, 2350 differential cases with 0 mismatches, 27 ind rows, 0 failures; review, domain and path regressions passed). L3 is by shape (Q-S5-5 (a)): the phase check of each `step` and the `Ind` matrix are the evidence; there is no kernel path term. Mutants: 8 of 8 KILLED (the S5 mutants table below). |
| S6 | `Trace`, `swap`, `++`, `[t]`, `[[ ]]`, `Blockchain`, `D`; X4 and X10 refused; `REFUSE_EQ_UNDECIDABLE`; L4, L9. | |
| S7 | `Ledger`, `apply`, `query`, `[[ ]]N`, `<=`, `Compatible`, Foata normal form; L6. | |
| S8 | `FinMap`, `canon`, `root`, inclusion proof, `UTxO`, `Valid`, `compose`; O1, O3; L7. | |
| S9 | T1 part 1: the Wasm step modules with their footprints; the notrap rows. | |
| S10 | T1 part 2: `quotientd`: the Wasm engine, SHA-256, BLS12-381, the mempool, the query answers, N6; the demo E1 to E6. | |
| S11 | T3: the JSON law report, `docs/REPORT-JSON.md`, the shard letters (X20). | |
| S12 | A1: canonical forms and `langc fmt`. | |
| S13 | A2: `langc check --json`. | |
| S14 | A4: `langc mcp`. | |
| S15 | A3 and A5: SKILL.md, G1 to G5, AGENTS.md and the README table final. | |
| S16 | A6: the token comparison. | |
| S17 | T2: the ZK circuit IR, ported from zkml-lang (Q-R8 (a)). | |
| S18 | Policy normal forms (D1 sec 12, Q-R7 (a)). | |
| S19 | Close: SPEC.md, probe/CAPABILITY.md, VALIDATION.md, final gate. | |

S3 mutants (12 rows; a serial `make -B check` for each mutant, then a
restore check and a serial gate): 11 KILLED, 1 EQUIVALENT.

| Mutant | Change | Result |
|---|---|---|
| PFIN-NONCOMM | `Pfin` is not in `bag_family` | KILLED: 3 FAIL rows (pfin-no-idem.lang and pfin-elim-no-idem.lang give TYPE_MISMATCH, and the message row) |
| PFIN-CLAUSE | `bag_clause` gives the `Bag` text at `Pfin` | KILLED: 1 FAIL row (the message row of pfin-no-idem.lang) |
| PFIN-IDEM-CELL | the boundary of `pfinIdem` at `~i` changes to `pIdemX` | KILLED: 369 FAIL rows (PATH_END in the domain at `pfinFold`) |
| IN-FOLD | `or` gives `b` on the right | KILLED: 369 FAIL rows (PATH_END in the domain at `orComm`) |
| L2-UNITL | one wrong path in `unionUnitL` | KILLED: 369 FAIL rows (PATH_END in the domain at `unionUnitL`) |
| L2-UNITR | one wrong path in `unionUnitR` | KILLED: 369 FAIL rows (PATH_END in the domain at `unionUnitR`) |
| L2-ASSOC | one wrong path in `unionAssoc` | KILLED: 369 FAIL rows (PATH_END in the domain at `unionAssoc`) |
| L2-COMM | one wrong path in `unionComm` | KILLED: 369 FAIL rows (PATH_END in the domain at `unionComm`) |
| L2-IDEM | one wrong path in `unionIdem` | KILLED: 369 FAIL rows (PATH_END in the domain at `unionIdem`) |
| KEY-FIRST-ORDER | `first_order_slot` admits `Asset` only | KILLED: 2 FAIL rows (sig-key-higher.lang gives exit 0, and its message row) |
| KEY-SPLICE-1 | no `key_after_key` call in `front_load` | KILLED: 4 FAIL rows (the footprint example and evals give NAME_UNKNOWN `Footprint`) |
| KEY-SPLICE-2 | no `key_after_key` call in `front_load_domain` | EQUIVALENT: exit 0, 0 FAIL rows; `langc` has no caller of `front_load_domain` (section 7, Q-S3-6 (a)) |

S4 mutants (15 rows; a serial `make -B check` for each mutant, then a
restore check and a serial gate): 14 KILLED, 1 EQUIVALENT.

| Mutant | Change | Result |
|---|---|---|
| AUTH-TRUNC | no `Trunc1` in `Authorized` | KILLED: 8 FAIL rows (TYPE_MISMATCH at the L5 lemma `authTxEq` in each program with the auth prelude) |
| AUTH-SPLICE-1 | no `auth_after_witness` call in `front_load` | KILLED: 8 FAIL rows (examples/authtx.lang and txid-authtx.lang give NAME_UNKNOWN `AuthTx`) |
| AUTH-SPLICE-2 | no `auth_after_witness` call in `front_load_domain` | EQUIVALENT: exit 0, 0 FAIL rows; `langc` has no caller of `front_load_domain` (section 7, as KEY-SPLICE-2, Q-S3-6 (a)) |
| L5-PATH | `authTxEq` applies `J` along the constant path at `witness x`, not along `p` | KILLED: 8 FAIL rows (TYPE_MISMATCH at `authTxEq`) |
| WITNESS-FIRST-ORDER | `first_order_slot` does not admit `Witness` | KILLED: 2 FAIL rows (witness-higher.lang gives exit 0, and its message row) |
| BODY-WITNESS | the `Body` check of law L5 is off | KILLED: 3 FAIL rows (body-has-witness.lang gives REFUSE_SIG, body-alias-witness.lang gives exit 0, and a message row) |
| TXID-TYPE | `program_type` admits each type of `txid` | KILLED: 4 FAIL rows (txid-reads-witness.lang and txid-authtx.lang give exit 0, and their message rows) |
| DIGEST-FIRST-ORDER | `first_order_slot` does not admit `Digest` | KILLED: 2 FAIL rows (digest-higher.lang gives exit 0, and its message row) |
| SIG-COMM | the check for a `Sig` slot with no `sigComm` is off | KILLED: 2 FAIL rows (sig-no-comm.lang gives exit 0, and its message row) |
| SIG-CLAUSE | the message of that check does not name `sigComm` or the commutative clause | KILLED: 1 FAIL row (the message row of sig-no-comm.lang) |
| AGG-SPLICE | no `agg_after_sig` call in `front_load` | KILLED: 4 FAIL rows (examples/agg.lang and its evals give NAME_UNKNOWN `agg`) |
| AGG-OP | the `aggOp` path is `sigMul (agg ys) (agg xs)` | KILLED: 9 FAIL rows (PATH_END at `aggOp` in each program with the agg prelude) |
| QC-QUORUM | `QC` has no quorum field | KILLED: 4 FAIL rows (examples/qc.lang and its evals give TYPE_INFER) |
| QC-SPLICE | no `qc_after_signs` call in `front_load` | KILLED: 4 FAIL rows (examples/qc.lang and its evals give NAME_UNKNOWN `QC`) |
| MEMPOOL-IN | the `AuthTx` equality of examples/authtx.lang compares the body of `x` with itself | KILLED: 6 FAIL rows (examples/authtx.lang and its `mempoolIn` rows) |

S5 mutants (8 rows; a serial `make -B check` for each mutant, then a
restore check and a serial gate): 8 KILLED.

| Mutant | Change | Result |
|---|---|---|
| IND-CONST-SKIP | `ind_meet` does not skip two constants that are not equal | KILLED: 1 FAIL row (the ind rows are not the rows of test/ind/expect.txt) |
| IND-PAIR-READS | `ind_pair` has no `reads a` x `writes b` half | KILLED: 1 FAIL row (the ind rows are not the rows of test/ind/expect.txt) |
| IND-CONST-NAME | `ind_const_same` compares two def names by name, not by value (Q-S5-33 (b)) | KILLED: 1 FAIL row (the ind rows are not the rows of test/ind/expect.txt) |
| IND-CLAUSE-SEEN | `ind_print` prints a clause again when it is equal to an earlier clause of its row | KILLED: 1 FAIL row (the ind rows are not the rows of test/ind/expect.txt) |
| FOOTPRINT-WITNESS | no `REFUSE_WITNESS_READ` for a footprint family that mentions `Witness` | KILLED: 4 FAIL rows (step-reads-witness.lang and step-reads-witness-alias.lang give exit 0; in the ind rows, step-reads-witness gives exit 0 and prints a row) |
| FOOTPRINT-SHAPE-CTORS | no `REFUSE_FOOTPRINT_SHAPE` for a family with a constructor count that is not 1 | KILLED: 1 FAIL row (footprint-shape-ctors.lang gives NAME_UNKNOWN for the pattern `Bal`, not REFUSE_FOOTPRINT_SHAPE) |
| BODY-SLOT-DEF | no `REFUSE_SIG` for a program def of `Body` with a footprint family (Q-S5-8 (a)) | KILLED: 2 FAIL rows (body-footprint.lang and body-footprint-before.lang give REFUSE_NAME, rule R4, not REFUSE_SIG) |
| KEYSPACE-CODOMAIN | no `REFUSE_KEYSPACE` for a key space with a codomain that is not `Key` (Q-S5-13 (a)) | KILLED: 1 FAIL row (keyspace-codomain.lang gives exit 0) |

## 13. Open items

- K1 D1 is in DESIGN.md as a digest only. A slice that needs a detail reads
  D1 again with the Claude Docs connector (DESIGN.md 4 gives the ids), and
  records the detail here. S2 (D1 sec 2 and 3, as built):
  `Value = Bag Asset`; `Balance = Asset -> Amount`; `[[ ]]v` is
  `valueBal`, a count by `valueCount`; `Delta` is the formal
  differences of `Value`, with the path `deltaEq` when
  `a + d = c + b`; `Balanced d` is a path to `deltaZero`; `+` on
  `Delta` is `deltaAdd` (section 4).
- K2 D1 marks these as not mechanized: the concat law (sec 1), `Balanced`
  (sec 3), `QC` (sec 4), the frame law (sec 7), the consensus colimit
  (sec 10), shards (sec 11), `FinMap` and `root` (sec 12). The checker of
  section 5 is the mechanization of the frame law for each program.
- K3 BLS12-381 and SHA-256 in C99 that TinyCC builds (S10). A BLS12-381
  tree in C is large. S10 surveys the sources (charter-lang has concrete
  crypto) and records the choice.
- K4 The Wasm engine of `quotientd` (S10): an own C99 interpreter for the
  MVP subset that `langc` emits (permit-lang Q-S0-1 precedent), or the
  merge-lang Wasm engine (merge-lang S7). S10 surveys.
- K5 SPEC.md is the kit text. It changes at each slice and is final at S19.
- K6 DONE (S2). The REFUSE_SIG table is the section 4 names (Q-S1-3
  (a)). The orbit-lang sample splice is gone from `src/front/front.c`
  (Q-S2-1 (a)). `domain/domain.lang` keeps the permit-lang 18deea2 kit
  names and adds `bagIsSet`, `bagFold`, `bagMap` and `Maybe`.
- K7 Kernel divergence (S2, Q-S2-7 (a)): `src/front/eval.c` differs
  from the permit-lang 18deea2 port by `conv_system_same`. The cover
  test of `conv_system` compares all pairs of branches in both
  directions, so its cost is exponential in the hcomp depth of
  `deltaExt` and `deltaAdd`. `conv_loop` tries `conv_system_same` (the
  same faces in the same order, and each pair of branches equal) first.
  A repin of the kernel must keep it.

## 14. Questions for the USER

The USER ruled Q-R1 to Q-R8 before S0 (2026-11-02, verbatim in section 1).
A slice that finds a new question adds it here as Q-Sn-m, with a
recommendation (a).

- Q-R1: R1 reading above. (a) accept.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R2: Rectification verdicts X1 to X21. (a) accept as written.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R3: Numbers (Balance uses N). (a) bounded u64 amounts with arithmetic
  typed as Maybe (overflow = abort value, never a trap); (b) arbitrary
  precision (allocation failure is then a runtime risk, so R0 needs a
  static size bound).
  RULED: (a), USER 11-02 (pre-S0).
- Q-R4: Canonical append (A1). (a) `c ++ [t]` only; fmt rewrites any
  append sugar; (b) `append t c` only.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R5: Footprint form. (a) static key patterns per body type, so Ind is
  decidable at compile time; (b) footprints computed from the body value at
  run time.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R6: QC (X15). (a) in v1 as a type with Pfin Node; (b) later slice.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R7: Policy normal forms (D1 sec 12, free distributive lattice, address
  = hash of the normal form; privacy cost). (a) later slice; (b) v1.
  RULED: (a), USER 11-02 (pre-S0).
- Q-R8: Seed kit. (a) tcc-wasm (Wasm STF + C node + langc mcp); ZK circuit
  IR as a later slice that ports zkml-lang Circuit IR.
  RULED: (a), USER 11-02 (pre-S0).
- Q-S1-1: Node rows. Review on 2026-11-02 restored the Wasm execution
  and differential checks in S1: 33 modules, 1088 cases, 0 mismatches.
  The gate covers every example and both scalar IR fixtures. Node is a
  gate dependency. The three targets still come at S9 (T1 part 1).
- Q-S1-2: The scope of REFUSE_NOT_IN_DESIGN. A program has one opaque
  declaration form, `axiom`, and families come from domain/domain.lang
  only. (a) path 1: an X4 or X10 name is refused in each declaration form
  and binder; path 2: an axiom of a universe type whose name is not an
  admitted base sort is refused; each other axiom keeps REFUSE_AXIOM, so
  the ported fixtures keep their codes; (b) refuse each axiom and each
  program type definition whose name section 4 does not admit.
  Recommendation: (a).
- Q-S1-3: The REFUSE_SIG table of the kernel is the orbit-lang sample
  signature (`Member`, `Choice`, `Outcome`, `Group`, `Orbit`, `act`,
  `menu` and others), not a section 4 name. Fixtures of the port use it.
  (a) keep it until the slice that gives the first section 4 slot (S2
  or S4), which replaces it with section 4 rows; (b) cut it in S1.
  Recommendation: (a).
  RULED: (a), USER 11-02 (S2 STEP 0): S2 replaces the rows.
- Q-S1-4: The section 5.4 "list of field inequalities" for a key space
  with more than one argument. For `allow(a.o, a.s)` against
  `allow(b.o, b.s)` the test is `a.o != b.o` OR `a.s != b.s`. (a) store
  an AND of OR-clauses (`IndClause`); a one-argument space gives clauses
  with one literal each; (b) allow only one-argument key spaces.
  Recommendation: (a).
  RULED: (a), USER 11-02 (S2 STEP 0).
- Q-S1-5: The `Pfin` idempotence cell. (a) `midem : (s : Pfin A) -> m s s
  = s`, which uses only recursive fields and passes the quorum cell rule;
  (b) the singleton form `m (eta x) (eta x) = eta x`, which can hit
  REFUSE_CELL. Recommendation: (a).
  RULED: (a), USER 11-02 (S2 STEP 0).
- Q-S1-6: Field access in a pattern. Section 5.1 writes `b.input`, but the
  kernel has no `.` token. (a) add `.` only inside a pattern and lower it
  to `proj_app`; (b) write `utxo (input b)` and change the 5.1 example.
  Recommendation: (a).
  RULED: (a), USER 11-02 (S2 STEP 0).
- Q-S2-1: The orbit-lang sample in src/front/front.c (the Orbit family
  after `act`, the DAO prelude after `outcomeSet`; K6). (a) S2 removes
  the splice and drops or rewrites the 15 check rows and 5 examples that
  use it; a kernel code that would lose its last row gets a row with
  section 4 names; (b) keep the splice to a later slice.
  RULED: (a), USER 11-02 (S2).
  DONE (S2): the splice is gone. S2 drops 13 obsolete check rows,
  3 examples and 16 eval rows, and rewrites 9 REFUSE_SIG fixtures.
  Review keeps the standalone signature example, the OrbitN theorem
  in bagorbit.lang, and the independent PATH_END rows beta-critical
  and perm-member0-wrong. Only the final DAO section of bagorbit.lang
  needs the removed Orbit splice.
- Q-S2-2: The form of `Amount`. (a) a nominal builtin type that a guest
  can use, with `amountAdd` and `amountSub` that give `Maybe Amount`
  (`none` at overflow and at underflow), an `Amount` literal form, and
  eval and lower ops; (b) a domain alias of `Nat`.
  RULED: (a), USER 11-02 (S2).
- Q-S2-3: `Asset` is a program slot, and domain/domain.lang loads before
  the program. (a) after a program defines `Asset`, the front end splices
  the value prelude (`Value`, `Balance`, `[[ ]]v`, `Delta`, `neg`,
  `Balanced`), as the orbit sample did after `act`; (b) each domain
  definition takes the asset type as a parameter.
  RULED: (a), USER 11-02 (S2).
- Q-S2-4: The scope of `REFUSE_BAG_NONCOMM`. Fold and elim cases are
  positional. (a) a fold or elim out of `Bag` with a wrong count of cases
  gives `REFUSE_BAG_NONCOMM`; other families keep `TYPE_MISMATCH`; (b)
  tag the cases, so that only a missing `comm` case gives it.
  RULED: (a), USER 11-02 (S2).
- Q-S2-5: the equality on `Asset` for `[[ ]]v`. RULED (a) by the USER,
  2026-11-02: a C builtin `valueCount` (eval only, as `len`) counts with
  the conversion check of the evaluator. `check_sig` requires that the
  `Asset` slot is first-order data (no path constructor, no function).
- Q-S2-6: L8, `Balanced` is closed under `+`. RULED (a) by the USER,
  2026-11-02: the prelude builds `deltaAdd` (a nested fold) and the path
  `balancedAdd`.
- Q-S2-7: the cost of `conv_system` at `balancedAdd`. RULED (a) by the
  USER, 2026-11-02: the kernel fast path `conv_system_same` in
  `src/front/eval.c`. The all-pairs cover test of `conv_system` is
  exponential in the hcomp depth of `deltaExt` and `deltaAdd`. The fast
  path accepts a pair only when the cover test also accepts it.
  `ARENA_LIMIT_BYTES` stays 1 GiB (section 13 K7).
- Q-S3-1: the form of `in`. A count is not well-defined on `Pfin` (the
  idem cell gives `m s s = s`). (a) an eval-only C builtin, as S2
  `valueCount`, with a first-order element type; (b) a prelude fold out
  of `Pfin A` into a 2-valued semilattice by `or`, with an equality from
  the program; (c) (a) at `Pfin Key` only.
  RULED: (b), USER 11-02 (S3). No C builtin. Q-S3-3 gives the carrier.
- Q-S3-2: `Key` and `Footprint`. (a) after a program defines the slot
  `Key`, the front end splices `Footprint = Pfin Key`, as the value
  prelude follows `Asset`; the `Key` slot must be first-order data
  (REFUSE_SIG, as `Asset`); `reads`, `writes` and key patterns (Q-S1-4,
  Q-S1-6) stay at S5; (b) defer `Footprint` to S5; (c) a domain def
  `Footprint (K : Type 0)` with no splice.
  RULED: (a), USER 11-02 (S3).
  DONE (S3): `key_after_key` in src/front/front.c, the rows
  sig-key-higher.lang and footprint-no-key.lang, examples/footprint.lang.
- Q-S3-3: the carrier of `in`. RULED (a) by the USER, 2026-11-02:
  `Bool` is a reserved name of the kernel (src/front/check.c), and the
  repo has no `Bool`, no `or` and no isSet proof of a 2-valued type. So
  the carrier is the bit `Sum Unit Unit`, with the domain defs `bfalse`,
  `btrue` and `or` and the `or` laws by elim. `isSet (Sum Unit Unit)`
  comes from a generic `discreteIsSet` (Hedberg), a port of quorum-lang
  lib/prelude.lang. No C change. `Bool` stays reserved.
- Q-S3-4 and Q-S3-5: the S3 records give no question with these ids.
- Q-S3-6: the mutant KEY-SPLICE-2 (no key splice in `front_load_domain`)
  lives. `langc` has no caller of `front_load_domain`: the guest mode
  and `--kit` both call `front_load`, and `--kit` sets only the check
  mode. `front_load_domain` is shared seed code. RULED (a) by the USER,
  2026-11-03: keep the splice in `front_load_domain`, record
  KEY-SPLICE-2 as an equivalent mutant (no caller), no source change
  (section 7).
- Q-S4-1: the form of the witness truncation. RULED (a) by the USER,
  2026-11-03 (S4): `Authorized b = Trunc1 (Sigma Witness (fun w => Path
  bit (witnessOk b w) btrue))`. `Body` and `Witness` are first-order
  program slots, and `witnessOk : Body -> Witness -> bit` is a program
  def. DONE (S4): the auth prelude, examples/authtx.lang.
- Q-S4-2: how REFUSE_WITNESS_READ finds a read. RULED (a): by type. The
  `Body` slot must not mention `Witness`, `Authorized` or `AuthTx`;
  `txid` has the kernel type `Body -> Digest` (S5: `step : Body ->
  Eff`). DONE (S4): four REFUSE_WITNESS_READ rows (section 7).
- Q-S4-3: `Digest`. RULED (a): a first-order program slot, as `Key` is
  (REFUSE_SIG). O3 stays a named assumption. DONE (S4):
  digest-higher.lang.
- Q-S4-4: `agg` and the commutative `Sig`. RULED (a): `Sig` is a slot,
  the program gives the six monoid names, and the front end splices
  `agg` (`bagFold`) and `aggOp`. No `sigComm`, or a wrong one, gives
  REFUSE_BAG_NONCOMM. DONE (S4): examples/agg.lang, sig-no-comm.lang,
  sig-comm-wrong.lang.
- Q-S4-5: the threshold of `QC b`. RULED (a): a program bit `quorum :
  Pfin Node -> bit` in the `Sigma`, outside the truncation. DONE (S4):
  the QC prelude, examples/qc.lang.
- Q-S4-6: the program names of the splices. RULED (a): one SIG row
  each, of a new kind (`SIG_PROGRAM`) with a type that the kernel fixes.
  A wrong type gives a named refusal. DONE (S4): section 4.
- Q-S4-7: the L5 law. RULED (a): the prelude lemma `authTxEq : (x y :
  AuthTx) -> Path Body (witness x) (witness y) -> Path AuthTx x y`; (b)
  `authSame` if the kernel has no Sigma eta. DONE (S4) as (a).
- Q-S4-8: the order of the build units. RULED (a): u2 the auth prelude,
  L5, REFUSE_WITNESS_READ and `Mempool`; u3 `Digest` and `txid`; u4
  `Sig` and `agg`; u5 `QC`; u6 this plan, the docs and the mutants; u7
  the close.
