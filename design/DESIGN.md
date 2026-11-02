# quotient-lang domain design

> Paste the domain design below the line, verbatim. Do not edit it.

This file is the only source of the core types and the core operations of
quotient-lang. `SPEC.md` sections 5 and 6 cite its sections. Do not add a core
type or a core operation that this file does not give.

When the design changes, paste the new version. Then record the change as an
open item in `SPEC.md` section 9.

---

## 1. The request (USER, 2026-11-02, verbatim)

I would like to write a new programming language with the following characteristics:

First, the language shall not allow a program to compile that leads to a runtime error, period.

In terms of type constructors/higher-kinded types, admit only cell monads and their duals as represented computationally in cubical type theory.

As for base types and operations admit only in what is the rectification of the following denotational designs: https://claude.ai/artifact/AwaABH27n1EfbBp6VPsiVb#7958bd30-0770, https://grok.com/share/c2hhcmQtMw_181d6280-2ca0-4a14-ab77-da3495933dad

The host language shall be TinyCC.  Use your judgment to provide multiple-choice option(s) for the compilation target(s).

Finally, I want agents to reach for this language when it fits their use case(s).  To that end, adhere to the following additional criteria:

<pasted 1>
  - one canonical form per operation and a langc fmt canonical printer;
  - langc check --json, giving fix hints and progress counts (parsed, typed, laws
    discharged);
  - a SKILL.md with 3 to 5 graded examples;
  - an MCP server written in TinyCC (langc mcp);
  - AGENTS.md and a README table saying when to use the language;
  - a token-count comparison against Python and Rust.
</pasted 1>

## 2. The S0 rulings (USER, 2026-11-02, AskUserQuestion, labels verbatim)

- Targets (multi-select): "Wasm STF + C node (Recommended)" (langc compiles each transaction body to a Wasm step function with its read/write footprint; a TinyCC-built C node applies traces, merges the mempool and answers queries; kit tcc-wasm, which also carries langc mcp), "ZK circuit IR (rollup)" (design sec 13: emit Valid r r' as a circuit, zkml-lang Circuit IR precedent, recursive compose), "JSON law report" (footprints, the Ind/D matrix, the MEV surface, each law discharged; binding as assumption). NOT chosen: "EVM bytecode".
- Crypto: "Abstract + v1 binds (Recommended)": one opaque Digest and one commutative Sig in the language, with their laws; binding stays a named assumption; v1 binds SHA-256 and BLS12-381 in the C node only.
- Grok design: "I will paste it": STOP before the seed; R2 is built from D1 and D2 at once.
- Name: "quotient-lang (Recommended)": private MavenRain/quotient-lang, seeded from lang-template.

## 3. Rectification of D1 and D2 (2026-11-02; Q-R1 to Q-R8 RULED (a) by the USER, 2026-11-02, before S0)

Verdicts: KEEP = both agree or D1-only and inside R0/R1; CORRECT = one design fixes the other (the fixed form wins); DROP = conflicts with R0 or R1, or is undefined. Cites: D1 secN; D2 para name.

| # | Name (admitted spelling) | D1 | D2 | Verdict and reason |
| --- | --- | --- | --- | --- |
| X1 | Body, AuthTx | sec 4 (Body, Authorized, AuthTx) | Semantic domain (Tx) | CORRECT: D2 Tx splits into Body + truncated witness; txid and effect read Body only (no-malleability) |
| X2 | Ind (footprint independence) | sec 7 (Bernstein: shared reads allowed) | Semantic domain (t1 perp t2: "non-overlapping reads/writes, distinct UTxOs, etc.") | CORRECT: D1 Bernstein form; D2 forbids shared reads (too strict) and "etc." is open (not a definition) |
| X3 | Trace (eps, <|, swap on Ind, trunc) | sec 8 | CTT realisation ("equivalently ... explicit path constructors for each generating relation (commutation ...)") | KEEP: D2's generator presentation = D1 Trace; generator = commutation ONLY |
| X4 | (absorption path) | sec 6 note (no idem on Trace; replay counts) | CTT realisation ("absorption of invalid or no-op transactions") | DROP as a generator: "invalid" depends on the state, so it is no path on histories; replay protection needs counting. The effect lives in X6 (an always-aborting history and a no-op are identified there by eval) |
| X5 | eval = [[ ]] : Trace -> Eff; Eff = State -> Maybe State, (f ; g) s = f s >>= g | secs 7, 8 (factors) | Semantic domain (eval), Operations (eval~ factors) | KEEP: same map; R0 reading: `nothing` = abort value |
| X6 | Blockchain = Im [[ ]] (Trace ->> Im [[ ]] -> Eff) | secs 9 (transition monoid), 13 (Im f = Sigma y trunc (fiber f y)) | Semantic domain (List Tx / ~ with the eval clause) | CORRECT: smallest congruence with the eval clause = ker eval, so List Tx / ~ = Im eval. D1's image factorization builds it without a decision procedure for "forall s, eval h1 s = eval h2 s" (not decidable over an infinite State; R0 refuses an equality test on it). Functions out of Blockchain = only those that factor through eval |
| X7 | ++, singleton [t] (monoid on Trace and Blockchain) | sec 8 ([[t ++ u]] = [[t]] . [[u]]) | Operations ([h1] . [h2] = [h1 ++ h2]; append t c = c . [t]) | KEEP; Q-R4 = one canonical spelling for append (A1) |
| X8 | Ledger = Trace / ~N (Nerode), apply, query, residual [[ ]]N | sec 9 | (none; D2 "Blockchain" is the finer, two-sided quotient) | KEEP: node state; right congruence is enough because a chain grows on the right |
| X9 | prefix <=, Compatible | sec 10 | Consensus ("agreement = path equality in Blockchain") | CORRECT: nodes at different heights are not equal; agreement = Compatible (common extension). Decidable on Trace when Ind is decidable (Foata normal form) |
| X10 | GenConsensus record, CanonicalChain = Forks / ~cons, run colimit | sec 10 | Consensus (CanonicalChain) | DROP from the language: quantifies over all n (no finite value), Forks and ~cons are undefined in D2. Stays as SPEC text in docs |
| X11 | Bag A (comm, trunc); Value = Bag Asset; Balance; [[ ]]v | sec 2 | Consensus para ("List Output / perm") | KEEP: same free commutative monoid; D1 generator presentation (one comm path clause per eliminator) |
| X12 | UTxO set = FinMap OutRef Output | secs 2 (coin identity lives in the history), 12 (FinMap, canon) | Consensus para (UTxO = List Output / perm) | CORRECT: outputs carry unique refs, so a UTxO set is a finite map keyed by OutRef, not a bag; State = Key -> Val covers it |
| X13 | Delta M = (M x M) / ~, neg, Balanced, mint/burn policy | sec 3 | (none) | KEEP: subtraction is total (no underflow), fits R0 |
| X14 | agg : Bag Sig -> Sig (commutative Sig, abstract) | sec 5 | (none) | KEEP: crypto ruling "Abstract + v1 binds" (BLS12-381 in the C node); a non-commutative scheme is REFUSED at Bag Sig |
| X15 | QC b (signer set outside, sigs inside the truncation) | sec 4 | (none) | KEEP (Q-R6: in v1 or later) |
| X16 | Pfin A (Kuratowski), _in_, union; Mempool = Pfin AuthTx | sec 6 | (none) | KEEP: gossip merge = union (state CRDT) |
| X17 | reads, writes : Body -> Pfin Key; frame law => commute | sec 7 | (none) | KEEP as the CORE checker feature: footprints are declared per body; the checker proves the frame law (step reads only reads, writes only writes, aborts from reads) and so derives commute. No program is admitted whose step breaks its footprint |
| X18 | FinMap Key Val, root = hashTrie . canon, inclusion proof, Digest (abstract) | sec 12 | (none) | KEEP; binding = named assumption O1 (crypto ruling); policy normal forms = Q-R7 |
| X19 | Valid r r', compose | sec 13 | (none) | KEEP: the ZK circuit IR target emits Valid; compose = recursive aggregation (uses X7 law + O1 once) |
| X20 | shards: Trace (B1 + B2) ~ Trace B1 x Trace B2 | sec 11 | (none) | KEEP as a JSON law report fact (cross-shard letter count), no new type |
| X21 | D = (Body x Body) minus Ind; MEV surface | sec 14 | Summary ("order-dependent bugs for commutative transactions are excluded by construction") | KEEP: both say the same; the JSON law report lists D pairs |

R1 reading (proposal, Q-R1): the HITs above (Bag, Pfin, Trace, Delta, FinMap, truncation) enter as R2 BASE types at fixed instances (Value = Bag Asset, Mempool = Pfin AuthTx, Footprint = Pfin Key, History = Trace over Body, ...). Programs cannot apply them to new types. The only program-level type constructors are a cell monad (the step computation, State -> Maybe State) and its dual (the ledger residual Trace -> Query -> Answer, a cofree-comonad behaviour), as R1 asks.

Q items for S1 (each with a proposed (a)):
- Q-R1: R1 reading above. (a) accept.
- Q-R2: Rectification verdicts X1 to X21. (a) accept as written.
- Q-R3: Numbers (Balance uses N). (a) bounded u64 amounts with arithmetic typed as Maybe (overflow = abort value, never a trap); (b) arbitrary precision (allocation failure is then a runtime risk, so R0 needs a static size bound).
- Q-R4: Canonical append (A1). (a) `c ++ [t]` only; fmt rewrites any append sugar; (b) `append t c` only.
- Q-R5: Footprint form. (a) static key patterns per body type, so Ind is decidable at compile time; (b) footprints computed from the body value at run time.
- Q-R6: QC (X15). (a) in v1 as a type with Pfin Node; (b) later slice.
- Q-R7: Policy normal forms (D1 sec 12, free distributive lattice, address = hash of the normal form; privacy cost). (a) later slice; (b) v1.
- Q-R8: Seed kit. (a) tcc-wasm (Wasm STF + C node + langc mcp); ZK circuit IR as a later slice that ports zkml-lang Circuit IR.

RULED (USER 2026-11-02, third message, verbatim): "Take the recommendation for Q-R1 through Q-R8, and give next session prompt". So Q-R1..Q-R8 = (a): R1 reading accepted; X1..X21 accepted as written; u64 amounts with Maybe arithmetic; canonical `c ++ [t]`; static footprint key patterns (Ind decidable at compile time); QC in v1; policy normal forms in a later slice; seed kit tcc-wasm, ZK circuit IR later slice.

## 4. D1 digest (Claude Docs "Quotient Chain", rev 3, read 2026-11-02)

D1 is the Claude Docs document "Quotient Chain" (project
5080d893-ae62-4b8c-b525-bd67200cc4ae, tab 7958bd30-0770, body node
f4621b7e-309d). This section is a digest, not the full text. Check marks
refer to the type-checked file QuotientChain.agda (Agda 2.7.0.1,
cubical-0.7, --cubical --safe).

Method (sec 0): every type gets a meaning simpler than itself; every operation obeys a morphism equation; rule: "if no observer can see a distinction, that distinction is a path constructor".

| Sec | Name | Form | Meaning / law | Status |
| --- | --- | --- | --- | --- |
| 1 | tower | Chain -> List Block -> List Body -> Trace -> Ledger -> Residual; Trace -> Eff | each arrow a surjective monoid map (quotient); forget certs, concat, [_]t, [_], semantics | concat law not mechanized |
| 2 | Bag A | HIT: []b, _::b_, comm, trunc | Value = Bag Asset; Balance = Asset -> N; [[ ]]v: [] = 0, xs (+) ys = sum pointwise | checked |
| 3 | Delta M | (M x M) / ~ with (a,b) ~ (c,d) iff a+d = c+b; neg | Delta Value = signed multi-asset amount; Z = Delta N; net effect d : Owner ->fin Delta Value; Balanced d = sum d = 0 (fee = delta to producer); mint/burn = only deltas outside the kernel (monetary policy) | Delta, neg checked; Balanced not |
| 4 | Authorized b | trunc-1 (Sigma Witness (Valid b)) | AuthTx = Sigma Body Authorized; no-malleability: equal bodies give equal AuthTx (txid ignores witnesses) | checked |
| 4 | QC b | Sigma Q : Pfin Node, 2f+1 <= size Q, trunc-1 (all v in Q -> Signed v b) | signer set outside the truncation (slashing), signatures inside | not mechanized |
| 5 | agg : Bag Sig -> Sig | one, x (x) agg xs, comm clause needs x(x)(y(x)z) = y(x)(x(x)z) | BLS fits (abelian); concatenated ECDSA must stay a List | checked |
| 6 | Pfin A | HIT: empty, singleton, union, nl, assoc, comm, idem, trunc; _in_ to hProp | Kuratowski-finite sets = free join-semilattice; gossip merge = union (state CRDT) | checked |
| 6 | (no idem on Trace) | | replay protection counts: a <| a <| t differs from a <| t | design note |
| 7 | State, Eff | [[State]] = Key -> Val; Eff = State -> Maybe State; (f ; g) s = f s >>= g, unit just | monoid | Eff monoid checked |
| 7 | reads, writes : Body -> Pfin Key; Ind a b | Bernstein: writes a # (reads b u writes b), writes b # reads a | frame law (step reads only reads, writes only writes, aborts from reads alone) implies commute: Ind a b -> step a ; step b = step b ; step a | commute = module parameter; frame law not mechanized |
| 8 | Trace | HIT: eps, a <| t, swap (Ind a b), trunc | free partially commutative monoid; [[ ]] : Trace -> M via act; laws [[t ++ u]] = [[t]] . [[u]], unique, factors | checked |
| 9 | Ledger | Trace / ~N, t ~N u iff all k, observe (t ++ k) = observe (u ++ k) | apply, query; [[ ]]N : Ledger -> (Trace -> Query -> Answer), injective; abs : R -> Ledger correct iff it commutes with apply, query | checked |
| 10 | prefix, Compatible, GenConsensus | t <= u = trunc (Sigma k, t ++ k = u); final, grows, safety | Lamport generalized consensus; independent-compatible | defs + lemma checked; colimit not |
| 11 | shards | Trace (B1 + B2) ~ Trace B1 x Trace B2 when footprints stay in one side | cross-shard letters = cost | not mechanized |
| 12 | FinMap Key Val, root | root = hashTrie . canon (canonical form = section of the quotient) | binding = root injective on the quotient; inclusion proof = truncated fiber; policy normal forms (free distributive lattice, antichains) | not mechanized |
| 13 | Valid r r' | trunc (Sigma s t s', root s = r, [[t]] s = just s', root s' = r') | compose (recursive aggregation) uses [[ ]]-++ and binding once | checked; binding = module parameter |
| 14 | D = (Body x Body) minus Ind | | dependent pairs keep order; MEV only inside D; hashes and signatures idealized (secs 4, 12) | design note |

## 5. D2 (Grok share "Denotational Blockchain Design in Cubical Type Theory Using Quotients", pasted by the USER 2026-11-02, verbatim)

Pasted by the USER 2026-11-02 (second message, claude3). Verbatim between the markers.

<pasted D2>
**Denotational design of a quotient-centric blockchain in Cubical Type Theory**

Following Conal Elliott’s methodology, we first fix a precise mathematical *meaning* (denotation) for the central types, independent of any representation or implementation. Correctness of any later implementation is then defined exactly by agreement with this denotation. The design maximises the use of quotients (realised as higher inductive types) so that observationally equivalent histories are identified by construction.

### Semantic domain

Let \(\mathsf{Tx}\) be the type of transactions and \(\mathsf{State}\) a type of observable states (account balances, UTxO sets, etc.). Write \(\mathsf{List}\,\mathsf{Tx}\) for the free monoid of transaction histories and let
\[
\mathsf{eval} : \mathsf{List}\,\mathsf{Tx} \to \mathsf{State} \to \mathsf{Maybe}\,\mathsf{State}
\]
be the (partial) evaluation map that applies a sequence from a given starting state.

Define the *observational equivalence* \(\sim\) on histories as the smallest congruence such that
- if \(t_1\perp t_2\) (independent: non-overlapping reads/writes, distinct UTxOs, etc.) then any context satisfies
  \[
  \dots\,t_1\,t_2\,\dots \;\sim\; \dots\,t_2\,t_1\,\dots,
  \]
- and, more globally,
  \[
  h_1\sim h_2 \quad\text{whenever}\quad
  \forall s.\;\mathsf{eval}\,h_1\,s\equiv\mathsf{eval}\,h_2\,s.
  \]
(The commutation relation already generates a large part of the kernel of \(\mathsf{eval}\).)

The denotation of a blockchain is an element of the set-quotient
\[
\llbracket\mathsf{Blockchain}\rrbracket \;=\; \mathsf{List}\,\mathsf{Tx}\,/\,\sim.
\]
Different linearisations of commutative transactions, or any two histories that produce identical observable outcomes, denote the *same* value.

### Cubical Type Theory realisation

In Cubical Type Theory the quotient is the higher inductive type

```text
data Blockchain : Type where
  [ _ ] : List Tx → Blockchain
  eq/   : {h1 h2 : List Tx} → (h1 ~ h2) → [ h1 ] ≡ [ h2 ]
  trunc : isSet Blockchain
```

(The set-truncation constructor guarantees that higher paths are trivial, so the type is a genuine set of equivalence classes.) Equivalently one may present the same type inductively with explicit path constructors for each generating relation (commutation of independent transactions, absorption of invalid or no-op transactions, \ldots) and then truncate.

The canonical meaning map from a concrete representation is simply the quotient constructor:
\[
\llbracket h\rrbracket \;=\; [h].
\]

### Operations and type-class morphisms

Because \(\sim\) is a congruence, the monoid structure of \(\mathsf{List}\,\mathsf{Tx}\) descends uniquely to the quotient. Consequently \(\mathsf{Blockchain}\) carries a monoid operation \(\cdot\) satisfying
\[
[h_1]\cdot[h_2] \;=\; [h_1\mathbin{++}h_2].
\]
Appending a single transaction is the special case
\[
\mathsf{append}\,t\,c \;=\; c\cdot[t].
\]
By the universal property of the quotient every operation on \(\mathsf{Blockchain}\) is forced by its action on representatives; in particular the type-class-morphism principle holds:
\[
\llbracket\mathsf{append}\,t\,c\rrbracket \;=\; \llbracket c\rrbracket\cdot[t].
\]
(The meaning of the operation is the operation on meanings.)

The evaluation map factors uniquely through the quotient:
\[
\mathsf{eval}_\sim : \mathsf{Blockchain} \to \mathsf{State}\to\mathsf{Maybe}\,\mathsf{State},
\quad
\mathsf{eval}_\sim\,[h] \;=\; \mathsf{eval}\,h.
\]
Thus the observable state is independent of the chosen representative.

### Consensus and further quotients

A concrete node may hold any representative of an equivalence class. Agreement among nodes is simply path equality in \(\mathsf{Blockchain}\). If a particular consensus rule (longest valid chain, voting, \ldots) is to be internalised, one may form a further quotient
\[
\mathsf{CanonicalChain} \;=\; \mathsf{Forks}\,/\,\sim_{\mathsf{cons}}
\]
where \(\sim_{\mathsf{cons}}\) identifies forks accepted as equal by the rule; the original observational quotient remains the fundamental denotation.

UTxO sets themselves may be realised as a prior quotient \(\mathsf{List}\,\mathsf{Output}\,/\,\mathsf{perm}\), so that the whole ledger is built by successive quotient constructions.

### Summary

The blockchain *is* the quotient monoid of transaction histories under observational equivalence. Every well-typed client program therefore manipulates equivalence classes rather than particular linearisations; order-dependent bugs for commutative transactions are excluded by construction. Any implementation (hash-linked blocks, DAGs, \ldots) is correct precisely when its operations agree with the corresponding operations on this quotient. The design is free of abstraction leaks, supplies the monoid laws for free, and is expressed entirely in the language of Cubical Type Theory.
</pasted D2>

## 6. Overlap (2026-11-02)

- No existing *-lang is a chain core. ledger-lang = CRM log schema (USER STOPPED it 10-24); not this.
- Port candidates, not homes: quorum-lang (FMSet ballots, CRDT, IVC: Pfin + rollup compose), merge-lang (semilattice merge laws, induction port S1b: Pfin union laws), zkml-lang Circuit IR (ZK target), zkpolicy-lang (ZK verifier), charter-lang (concrete crypto, if a later slice wants it), permit-lang (R0 deny-as-value, R1 table, A1 to A6 shape).
