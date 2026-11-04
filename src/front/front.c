#include <string.h>

#include "front/front.h"

static int load_one(Arena *arena, const char *source, Origin origin, const char *text, size_t len, DeclList *out, Diag *diag) {
  TokenList toks;
  if (!lex_source(arena, source, text, len, &toks, diag)) return 0;
  return parse_source(arena, source, origin, &toks, out, diag);
}

/* The value prelude (quotient-lang S2, USER ruling Q-S2-3 (a); PLAN
   sections 4 and 6). Asset is a program slot and the domain file loads
   before the program, so the front end puts these kernel declarations
   directly after the program def Asset. Value is Bag Asset. Delta is the
   formal differences of Value (D1 sec 3, the instance Net of PLAN section
   3): deltaEq is a path from deltaOf a b to deltaOf c d when a + d = c + b,
   and deltaSquash makes Delta a set. deltaSub is a - b and is total (X13).
   neg swaps the two sides. Balanced d is a path from d to deltaZero. The
   L8 paths: deltaSelf (a - a = 0) and balancedNeg. Balance is Asset ->
   Amount; valueBal is [[ ]]v, the count of each asset (valueCount, USER
   ruling Q-S2-5 (a)); balanceAdd adds two balances at an asset.
   deltaAdd adds two differences: a fold on x into Delta -> Delta, with
   deltaExt (an elim into a family of paths in the set Delta) as the path
   case (USER ruling Q-S2-6 (a)); balancedAdd is law L8 under +. */
#define VALUE_SOURCE_NAME "kernel/value.lang"

static const char value_source[] =
  "def Value : Type 0 := Bag Asset\n"
  "family Delta := deltaOf (deltaPos : Value) (deltaNeg : Value)\n"
  "  | deltaEq (eqPosA : Value) (eqNegA : Value) (eqPosB : Value) (eqNegB : Value) (eqWit : Path Value (bagOp Asset eqPosA eqNegB) (bagOp Asset eqPosB eqNegA)) (i : I)\n"
  "    [ ~i -> deltaOf eqPosA eqNegA, i -> deltaOf eqPosB eqNegB ]\n"
  "  | deltaSquash (deltaFrom : Delta) (deltaTo : Delta) (deltaLeft : Path Delta deltaFrom deltaTo) (deltaRight : Path Delta deltaFrom deltaTo) (i : I) (j : I)\n"
  "    [ ~i -> deltaLeft @ j, i -> deltaRight @ j, ~j -> deltaFrom, j -> deltaTo ]\n"
  "def deltaIsSet : isSet Delta :=\n"
  "  fun (x : Delta) (y : Delta) (p : Path Delta x y) (q : Path Delta x y) => fun (i : I) => fun (j : I) => deltaSquash x y p q i j\n"
  "def deltaZero : Delta := deltaOf (bagUnit Asset) (bagUnit Asset)\n"
  "def deltaSub : Value -> Value -> Delta := fun (a : Value) (b : Value) => deltaOf a b\n"
  "def neg : Delta -> Delta :=\n"
  "  fun (z : Delta) => fold (fun (p : Value) (n : Value) => deltaOf n p)\n"
  "    (fun (a : Value) (b : Value) (c : Value) (d : Value) (r : Path Value (bagOp Asset a d) (bagOp Asset c b)) =>\n"
  "      fun (i : I) => deltaEq b a d c (trans Value (bagOp Asset b c) (bagOp Asset c b) (bagOp Asset d a) (fun (k : I) => bagComm Asset b c k)\n"
  "        (trans Value (bagOp Asset c b) (bagOp Asset a d) (bagOp Asset d a) (fun (k : I) => r @ (~k)) (fun (k : I) => bagComm Asset a d k))) i)\n"
  "    (fun (x : Delta) (y : Delta) (p : Path Delta x y) (q : Path Delta x y) => fun (i : I) => fun (j : I) => (deltaIsSet x y p q @ i) @ j) z\n"
  "def Balanced : Delta -> Type 0 := fun (d : Delta) => Path Delta d deltaZero\n"
  "def deltaSelf : (a : Value) -> Balanced (deltaSub a a) :=\n"
  "  fun (a : Value) => fun (i : I) => deltaEq a a (bagUnit Asset) (bagUnit Asset) (fun (k : I) => bagComm Asset a (bagUnit Asset) k) i\n"
  "def balancedNeg : (d : Delta) -> Balanced d -> Balanced (neg d) :=\n"
  "  fun (d : Delta) (p : Balanced d) => fun (i : I) => neg (p @ i)\n"
  "def Balance : Type 0 := Asset -> Amount\n"
  "def valueBal : Value -> Balance := fun (v : Value) (a : Asset) => valueCount Asset v a\n"
  "def balanceAdd : Balance -> Balance -> Asset -> Maybe Amount :=\n"
  "  fun (f : Balance) (g : Balance) (a : Asset) => amountAdd (f a) (g a)\n"
  "def valueSwap : (x : Value) -> (y : Value) -> (z : Value) -> (w : Value) -> Path Value (bagOp Asset (bagOp Asset x y) (bagOp Asset z w)) (bagOp Asset (bagOp Asset x z) (bagOp Asset y w)) :=\n"
  "  fun (x : Value) (y : Value) (z : Value) (w : Value) =>\n"
  "    trans Value (bagOp Asset (bagOp Asset x y) (bagOp Asset z w)) (bagOp Asset x (bagOp Asset y (bagOp Asset z w))) (bagOp Asset (bagOp Asset x z) (bagOp Asset y w)) (fun (k : I) => bagAssoc Asset x y (bagOp Asset z w) k)\n"
  "      (trans Value (bagOp Asset x (bagOp Asset y (bagOp Asset z w))) (bagOp Asset x (bagOp Asset (bagOp Asset y z) w)) (bagOp Asset (bagOp Asset x z) (bagOp Asset y w)) (fun (k : I) => bagOp Asset x (bagAssoc Asset y z w (~k)))\n"
  "        (trans Value (bagOp Asset x (bagOp Asset (bagOp Asset y z) w)) (bagOp Asset x (bagOp Asset (bagOp Asset z y) w)) (bagOp Asset (bagOp Asset x z) (bagOp Asset y w)) (fun (k : I) => bagOp Asset x (bagOp Asset (bagComm Asset y z k) w)) (trans Value (bagOp Asset x (bagOp Asset (bagOp Asset z y) w)) (bagOp Asset x (bagOp Asset z (bagOp Asset y w))) (bagOp Asset (bagOp Asset x z) (bagOp Asset y w)) (fun (k : I) => bagOp Asset x (bagAssoc Asset z y w k)) (fun (k : I) => bagAssoc Asset x z (bagOp Asset y w) (~k)))))\n"
  "def deltaShift : Value -> Value -> Delta -> Delta :=\n"
  "  fun (a : Value) (b : Value) (y : Delta) => fold (fun (c : Value) (d : Value) => deltaOf (bagOp Asset a c) (bagOp Asset b d))\n"
  "    (fun (c : Value) (d : Value) (c2 : Value) (d2 : Value) (r : Path Value (bagOp Asset c d2) (bagOp Asset c2 d)) =>\n"
  "      fun (i : I) => deltaEq (bagOp Asset a c) (bagOp Asset b d) (bagOp Asset a c2) (bagOp Asset b d2) (trans Value (bagOp Asset (bagOp Asset a c) (bagOp Asset b d2)) (bagOp Asset (bagOp Asset a b) (bagOp Asset c d2)) (bagOp Asset (bagOp Asset a c2) (bagOp Asset b d)) (valueSwap a c b d2)\n"
  "        (trans Value (bagOp Asset (bagOp Asset a b) (bagOp Asset c d2)) (bagOp Asset (bagOp Asset a b) (bagOp Asset c2 d)) (bagOp Asset (bagOp Asset a c2) (bagOp Asset b d)) (fun (k : I) => bagOp Asset (bagOp Asset a b) (r @ k)) (fun (k : I) => valueSwap a c2 b d @ (~k)))) i)\n"
  "    (fun (x : Delta) (z : Delta) (p : Path Delta x z) (q : Path Delta x z) => fun (i : I) => fun (j : I) => (deltaIsSet x z p q @ i) @ j) y\n"
  "def deltaExt : (T : Type 0) -> isSet T -> (L : Delta -> T) -> (M : Delta -> T) -> ((a : Value) -> (b : Value) -> Path T (L (deltaOf a b)) (M (deltaOf a b))) -> (z : Delta) -> Path T (L z) (M z) :=\n"
  "  fun (T : Type 0) (sT : isSet T) (L : Delta -> T) (M : Delta -> T) (h : (a : Value) -> (b : Value) -> Path T (L (deltaOf a b)) (M (deltaOf a b))) (z : Delta) =>\n"
  "    elim (fun (t : Delta) => Path T (L t) (M t)) (fun (a : Value) (b : Value) => h a b)\n"
  "      (fun (a : Value) (b : Value) (c : Value) (d : Value) (w : Path Value (bagOp Asset a d) (bagOp Asset c b)) =>\n"
  "        fun (j : I) => hcomp (Path T (L (deltaEq a b c d w j)) (M (deltaEq a b c d w j))) (~j \\/ j) (fun (k : I) => [\n"
  "          ~j -> sT (L (deltaEq a b c d w j)) (M (deltaEq a b c d w j)) (transp (fun (m : I) => Path T (L (deltaEq a b c d w (j /\\ m))) (M (deltaEq a b c d w (j /\\ m)))) i0 (h a b)) (h a b) @ k,\n"
  "          j -> sT (L (deltaEq a b c d w j)) (M (deltaEq a b c d w j)) (transp (fun (m : I) => Path T (L (deltaEq a b c d w (j /\\ m))) (M (deltaEq a b c d w (j /\\ m)))) i0 (h a b)) (h c d) @ k ]) (transp (fun (m : I) => Path T (L (deltaEq a b c d w (j /\\ m))) (M (deltaEq a b c d w (j /\\ m)))) i0 (h a b)))\n"
  "      (fun (x : Delta) (ihx : Path T (L x) (M x)) (y : Delta) (ihy : Path T (L y) (M y))\n"
  "        (p : Path Delta x y) (ihp : PathP (fun (j : I) => Path T (L (p @ j)) (M (p @ j))) ihx ihy)\n"
  "        (q : Path Delta x y) (ihq : PathP (fun (j : I) => Path T (L (q @ j)) (M (q @ j))) ihx ihy) =>\n"
  "        fun (i : I) => fun (j : I) => hcomp (Path T (L (deltaSquash x y p q i j)) (M (deltaSquash x y p q i j))) (~i \\/ i \\/ ~j \\/ j) (fun (k : I) => [\n"
  "          ~i -> sT (L (deltaSquash x y p q i j)) (M (deltaSquash x y p q i j)) (transp (fun (m : I) => Path T (L (deltaSquash x y p q (i /\\ m) (j /\\ m))) (M (deltaSquash x y p q (i /\\ m) (j /\\ m)))) i0 ihx) (ihp @ j) @ k,\n"
  "          i -> sT (L (deltaSquash x y p q i j)) (M (deltaSquash x y p q i j)) (transp (fun (m : I) => Path T (L (deltaSquash x y p q (i /\\ m) (j /\\ m))) (M (deltaSquash x y p q (i /\\ m) (j /\\ m)))) i0 ihx) (ihq @ j) @ k,\n"
  "          ~j -> sT (L (deltaSquash x y p q i j)) (M (deltaSquash x y p q i j)) (transp (fun (m : I) => Path T (L (deltaSquash x y p q (i /\\ m) (j /\\ m))) (M (deltaSquash x y p q (i /\\ m) (j /\\ m)))) i0 ihx) ihx @ k,\n"
  "          j -> sT (L (deltaSquash x y p q i j)) (M (deltaSquash x y p q i j)) (transp (fun (m : I) => Path T (L (deltaSquash x y p q (i /\\ m) (j /\\ m))) (M (deltaSquash x y p q (i /\\ m) (j /\\ m)))) i0 ihx) ihy @ k ]) (transp (fun (m : I) => Path T (L (deltaSquash x y p q (i /\\ m) (j /\\ m))) (M (deltaSquash x y p q (i /\\ m) (j /\\ m)))) i0 ihx)) z\n"
  "def deltaAdd : Delta -> Delta -> Delta :=\n"
  "  fun (x : Delta) => fold (fun (a : Value) (b : Value) => deltaShift a b)\n"
  "    (fun (a : Value) (b : Value) (c : Value) (d : Value) (r : Path Value (bagOp Asset a d) (bagOp Asset c b)) =>\n"
  "      fun (i : I) => fun (y : Delta) => deltaExt Delta deltaIsSet (deltaShift a b) (deltaShift c d)\n"
  "        (fun (e : Value) (f : Value) => fun (k : I) => deltaEq (bagOp Asset a e) (bagOp Asset b f) (bagOp Asset c e) (bagOp Asset d f) (trans Value (bagOp Asset (bagOp Asset a e) (bagOp Asset d f)) (bagOp Asset (bagOp Asset a d) (bagOp Asset e f)) (bagOp Asset (bagOp Asset c e) (bagOp Asset b f)) (valueSwap a e d f) (trans Value (bagOp Asset (bagOp Asset a d) (bagOp Asset e f)) (bagOp Asset (bagOp Asset c b) (bagOp Asset e f)) (bagOp Asset (bagOp Asset c e) (bagOp Asset b f)) (fun (k : I) => bagOp Asset (r @ k) (bagOp Asset e f)) (valueSwap c b e f))) k) y @ i)\n"
  "    (fun (F : Delta -> Delta) (G : Delta -> Delta) (P : Path (Delta -> Delta) F G) (R : Path (Delta -> Delta) F G) =>\n"
  "      fun (i : I) => fun (j : I) => fun (y : Delta) => deltaSquash (F y) (G y) (fun (k : I) => (P @ k) y) (fun (k : I) => (R @ k) y) i j) x\n"
  "def deltaAddZero : Path Delta (deltaAdd deltaZero deltaZero) deltaZero :=\n"
  "  fun (i : I) => deltaEq (bagOp Asset (bagUnit Asset) (bagUnit Asset)) (bagOp Asset (bagUnit Asset) (bagUnit Asset)) (bagUnit Asset) (bagUnit Asset) (fun (k : I) => bagAssoc Asset (bagUnit Asset) (bagUnit Asset) (bagUnit Asset) k) i\n"
  "def balancedAdd : (x : Delta) -> (y : Delta) -> Balanced x -> Balanced y -> Balanced (deltaAdd x y) :=\n"
  "  fun (x : Delta) (y : Delta) (p : Balanced x) (q : Balanced y) =>\n"
  "    trans Delta (deltaAdd x y) (deltaAdd deltaZero deltaZero) deltaZero (fun (i : I) => deltaAdd (p @ i) (q @ i)) deltaAddZero\n";

/* The first definition or family named NAME in OUT from FIRST on, or
   OUT->count. */
static size_t def_at(const DeclList *out, size_t first, const char *name) {
  size_t at;
  for (at = first; at < out->count && ((out->items[at].kind != DECL_DEF && out->items[at].kind != DECL_FAMILY) || strcmp(out->items[at].name, name) != 0); at++)
    ;
  return at;
}

/* When OUT from FIRST on defines each of the COUNT names AFTER, put the
   kernel declarations of TEXT directly after the last of them, with the
   trusted origin ORIGIN_DOMAIN. Check order is declaration order, so a
   refused slot stops before them. */
static int splice_after(Arena *arena, size_t first, const char *const *after, size_t count, const char *source, const char *text, size_t len, DeclList *out, Diag *diag) {
  DeclList kernel = {NULL, 0, 0};
  Decl *items;
  size_t at = first;
  size_t i;
  for (i = 0; i < count; i++) {
    size_t k = def_at(out, first, after[i]);
    if (k == out->count)
      return 1;
    at = k > at ? k : at;
  }
  if (!load_one(arena, source, ORIGIN_DOMAIN, text, len, &kernel, diag))
    return 0;
  items = arena_alloc(arena, (out->count + kernel.count) * sizeof *items);
  if (items == NULL)
    return 0;
  memcpy(items, out->items, (at + 1u) * sizeof *items);
  memcpy(items + at + 1u, kernel.items, kernel.count * sizeof *items);
  memcpy(items + at + 1u + kernel.count, out->items + at + 1u, (out->count - at - 1u) * sizeof *items);
  out->items = items;
  out->count += kernel.count;
  out->cap = out->count;
  return 1;
}

static const char *const VALUE_AFTER[] = {"Asset"};

/* The value prelude goes directly after the program def Asset. */
static int value_after_asset(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, VALUE_AFTER, 1u, VALUE_SOURCE_NAME, value_source, sizeof value_source - 1u, out, diag);
}

/* The key prelude (quotient-lang S3, USER ruling Q-S3-2 (a); PLAN section
   4). Key is a program slot, so the front end puts the def Footprint
   directly after Key: the program def Key or, with a key space in the
   program, the family Key that key_family makes (Q-S5-23 (a), Q-S5-24
   (a)). A footprint is a finite subset of keys. The Key slot must be
   first-order data (check.c, check_sig). */
#define KEY_SOURCE_NAME "kernel/key.lang"

static const char key_source[] =
  "def Footprint : Type 0 := Pfin Key\n";

static const char *const KEY_AFTER[] = {"Key"};

/* The key prelude goes directly after Key (the program def or the
   generated family). */
static int key_after_key(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, KEY_AFTER, 1u, KEY_SOURCE_NAME, key_source, sizeof key_source - 1u, out, diag);
}

/* The step prelude (quotient-lang S5, USER rulings Q-S5-3 (a), Q-S5-7 (a)
   and Q-S5-18 (a); survey section 2). Key and Val are program slots, so
   the front end puts these defs directly after the last of the program
   defs Key and Val. A state gives the value at each key. An effect is a
   partial map of states: nothing is the abort value. effSeq is the
   Kleisli composite (the DESIGN notation f ; g) and just is its unit.
   effRun is the N3 run rule: an aborted step keeps the state s. */
#define STEP_SOURCE_NAME "kernel/step.lang"

static const char step_source[] =
  "def State : Type 0 := Key -> Val\n"
  "def Eff : Type 0 := State -> Maybe State\n"
  "def just : Eff := fun (s : State) => some s\n"
  "def effSeq : Eff -> Eff -> Eff := fun (f : Eff) (g : Eff) (s : State) => bind (f s) (fun (t : State) => g t)\n"
  "def effRun : Eff -> State -> State := fun (f : Eff) (s : State) => option s (fun (t : State) => t) (f s)\n";

static const char *const STEP_AFTER[] = {"Key", "Val"};

/* The step prelude goes directly after the last of the program defs Key
   and Val. */
static int step_after_val(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, STEP_AFTER, 2u, STEP_SOURCE_NAME, step_source, sizeof step_source - 1u, out, diag);
}

/* The auth prelude (quotient-lang S4, USER rulings Q-S4-1 (a) and Q-S4-7
   (a); PLAN sections 4 and 6). Body and Witness are program slots and
   witnessOk is a program def with a kernel-fixed type (check.c,
   check_sig). After the last of them, the front end puts the defs
   Authorized, AuthTx, Mempool and the law L5 lemma authTxEq: two
   authorized transactions with one body are one transaction, so the
   witness does not count. */
#define AUTH_SOURCE_NAME "kernel/auth.lang"

static const char auth_source[] =
  "def Authorized : Body -> Type 0 := fun (b : Body) =>\n"
  "  Trunc1 (Sigma (w : Witness) (Path (Sum Unit Unit) (witnessOk b w) btrue))\n"
  "def AuthTx : Type 0 := Sigma (b : Body) (Authorized b)\n"
  "def Mempool : Type 0 := Pfin AuthTx\n"
  "def authTxEq : (x : AuthTx) -> (y : AuthTx) -> Path Body (witness x) (witness y) -> Path AuthTx x y :=\n"
  "  fun (x : AuthTx) (y : AuthTx) (p : Path Body (witness x) (witness y)) =>\n"
  "    J Body (witness x)\n"
  "      (fun (c : Body) (q : Path Body (witness x) c) => (v : Authorized c) -> Path AuthTx x (pack c v))\n"
  "      (fun (v : Authorized (witness x)) => fun (i : I) => pack (witness x) (squash1 (Sigma (w : Witness) (Path (Sum Unit Unit) (witnessOk (witness x) w) btrue)) (payload x) v i))\n"
  "      (witness y) p (payload y)\n";

static const char *const AUTH_AFTER[] = {"Body", "Witness", "witnessOk"};

/* The auth prelude goes directly after the last of the program defs Body,
   Witness and witnessOk. */
static int auth_after_witness(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, AUTH_AFTER, 3u, AUTH_SOURCE_NAME, auth_source, sizeof auth_source - 1u, out, diag);
}

/* The agg prelude (quotient-lang S4, USER rulings Q-S4-4 (a) and Q-S4-6
   (a); PLAN section 4, law L1). Sig is a program slot, and sigIsSet,
   sigOne, sigMul, sigAssoc, sigComm and sigUnitL are program defs with
   the types of the bagFold arguments at Sig (check.c, check_sig). After
   the last of them, the front end puts agg, the fold of a bag of
   signatures into one signature, and the law L1 lemma aggOp: agg takes
   the bag union to sigMul. */
#define AGG_SOURCE_NAME "kernel/agg.lang"

static const char agg_source[] =
  "def agg : Bag Sig -> Sig := fun (s : Bag Sig) =>\n"
  "  bagFold Sig Sig sigIsSet sigOne sigMul sigAssoc sigComm sigUnitL (fun (x : Sig) => x) s\n"
  "def aggOp : (xs : Bag Sig) -> (ys : Bag Sig) -> Path Sig (agg (bagOp Sig xs ys)) (sigMul (agg xs) (agg ys)) :=\n"
  "  fun (xs : Bag Sig) (ys : Bag Sig) => fun (i : I) => sigMul (agg xs) (agg ys)\n";

static const char *const AGG_AFTER[] = {"Sig", "sigIsSet", "sigOne", "sigMul", "sigAssoc", "sigComm", "sigUnitL"};

/* The agg prelude goes directly after the last of the program defs Sig
   and the six bagFold arguments. */
static int agg_after_sig(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, AGG_AFTER, 7u, AGG_SOURCE_NAME, agg_source, sizeof agg_source - 1u, out, diag);
}

/* The QC prelude (quotient-lang S4, USER ruling Q-S4-5 (a); PLAN section
   4, X15). Node, Body and Sig are program slots, and nodeEq, quorum and
   signs are program defs with kernel-fixed types (check.c, check_sig).
   After the last of them, the front end puts QC: a quorum certificate on
   a body is a set of nodes that is a quorum, and a proof that each node
   of the set signs the body. The C node checks 2f+1 at S10. */
#define QC_SOURCE_NAME "kernel/qc.lang"

static const char qc_source[] =
  "def QC : Body -> Type 0 := fun (b : Body) =>\n"
  "  Sigma (q : Pfin Node) (Sigma (h : Path (Sum Unit Unit) (quorum q) btrue)\n"
  "    (Trunc1 ((v : Node) -> Path (Sum Unit Unit) (pfinIn Node nodeEq v q) btrue ->\n"
  "      Sigma (s : Sig) (Path (Sum Unit Unit) (signs v b s) btrue))))\n";

static const char *const QC_AFTER[] = {"Node", "Body", "Sig", "nodeEq", "quorum", "signs"};

/* The QC prelude goes directly after the last of the program defs Node,
   Body, Sig, nodeEq, quorum and signs. */
static int qc_after_signs(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, QC_AFTER, 6u, QC_SOURCE_NAME, qc_source, sizeof qc_source - 1u, out, diag);
}

/* The Key family (quotient-lang S5, USER rulings Q-S5-23 (a) and Q-S5-24
   (a)). With a key space in the program, Key is a family with one
   constructor for each key space, in the order of the keyspace
   declarations: `keyspace Bal : Size -> Key` gives the constructor Bal
   with one Size field. A field name is the space name, '#' and the
   position from 1 (Bal#1). The lexer cannot make such a name, so no
   program name clashes with a field. */
static const char *key_field_name(Arena *arena, const char *space, size_t pos) {
  size_t len = strlen(space);
  size_t end = len + 2u;
  size_t at;
  size_t v;
  char *s;
  for (v = pos; v >= 10u; v /= 10u)
    end++;
  s = arena_alloc(arena, end + 1u);
  if (s == NULL)
    return NULL;
  memcpy(s, space, len);
  s[len] = '#';
  s[end] = '\0';
  for (v = pos, at = end; at > len + 1u; v /= 10u)
    s[--at] = (char)('0' + (int)(v % 10u));
  return s;
}

/* The key-eq prelude (quotient-lang S5, USER ruling Q-S5-25 (a)). With a
   key space in the program, the front end makes keyEq : Key -> Key ->
   Flag (Q-S5-23 (a)): two keys are equal when they have the same key
   space and equal arguments. The fixed defs give an eq for each key
   argument form; each parametric eq takes an eq for its argument types.
   A fold of a List is `fold STEP BASE l`, so listEq binds the uncons fold
   to the typed name un. */
#define KEY_EQ_SOURCE_NAME "kernel/key-eq.lang"

static const char key_eq_source[] =
  "def flagEq : Flag -> Flag -> Flag := fun (a : Flag) (b : Flag) => flagIf a b (flagIf b flagNo flagYes)\n"
  "def sizeEq : Size -> Size -> Flag := fun (a : Size) => fold (fun (b : Size) => elim (fun (t : Size) => Flag) flagYes (fun (k : Size) (ih : Flag) => flagNo) b) (fun (r : Size -> Flag) (b : Size) => elim (fun (t : Size) => Flag) flagNo (fun (k : Size) (ih : Flag) => r k) b) a\n"
  "def optionEq : (A : Type 0) -> (A -> A -> Flag) -> Option A -> Option A -> Flag := fun (A : Type 0) (eqA : A -> A -> Flag) (x : Option A) (y : Option A) => option (option flagYes (fun (b : A) => flagNo) y) (fun (a : A) => option flagNo (fun (b : A) => eqA a b) y) x\n"
  "def prodEq : (A : Type 0) -> (B : Type 0) -> (A -> A -> Flag) -> (B -> B -> Flag) -> Prod A B -> Prod A B -> Flag := fun (A : Type 0) (B : Type 0) (eqA : A -> A -> Flag) (eqB : B -> B -> Flag) (x : Prod A B) (y : Prod A B) => flagIf (eqA (first x) (first y)) (eqB (second x) (second y)) flagNo\n"
  "def listEq : (A : Type 0) -> (A -> A -> Flag) -> List A -> List A -> Flag := fun (A : Type 0) (eqA : A -> A -> Flag) (xs : List A) (ys : List A) => (fun (un : List A -> Option (Prod A (List A))) => fold (fun (h : A) (r : List A -> Flag) (zs : List A) => option flagNo (fun (p : Prod A (List A)) => flagIf (eqA h (first p)) (r (second p)) flagNo) (un zs)) (fun (zs : List A) => option flagYes (fun (p : Prod A (List A)) => flagNo) (un zs)) xs ys) (fun (l : List A) => fold (fun (g : A) (acc : Option (Prod A (List A))) => some (pair g (option nil (fun (q : Prod A (List A)) => cons (first q) (second q)) acc))) none l)\n";

/* Q-S5-25 (a): the same test as key_arg_form in check.c (the rule
   REFUSE_KEYSPACE). The key-eq prelude prints only these forms. */
static int key_arg_form(const Term *t) {
  const Term *head;
  if (t == NULL)
    return 0;
  if (t->kind == TERM_VAR)
    return t->name != NULL && (strcmp(t->name, "Nat") == 0 || strcmp(t->name, "Size") == 0 || strcmp(t->name, "Flag") == 0);
  if (t->kind != TERM_APP || t->left == NULL)
    return 0;
  head = t->left;
  if (head->kind == TERM_VAR && head->name != NULL && (strcmp(head->name, "Option") == 0 || strcmp(head->name, "List") == 0))
    return key_arg_form(t->right);
  if (head->kind != TERM_APP || head->left == NULL || head->left->kind != TERM_VAR || head->left->name == NULL || strcmp(head->left->name, "Prod") != 0)
    return 0;
  return key_arg_form(head->right) && key_arg_form(t->right);
}

/* An arena text buffer for the keyEq def. A failed allocation clears ok. */
typedef struct {
  Arena *arena;
  char *buf;
  size_t len;
  size_t cap;
  int ok;
} KeyText;

static int key_text_grow(KeyText *b, size_t need) {
  size_t cap = b->cap * 2u;
  char *grown;
  for (; cap < need; cap *= 2u)
    ;
  grown = arena_alloc(b->arena, cap);
  if (grown == NULL)
    return 0;
  memcpy(grown, b->buf, b->len + 1u);
  b->buf = grown;
  b->cap = cap;
  return 1;
}

static void key_put(KeyText *b, const char *s) {
  size_t n = strlen(s);
  b->ok = b->ok && (b->len + n + 1u <= b->cap || key_text_grow(b, b->len + n + 1u));
  if (!b->ok)
    return;
  memcpy(b->buf + b->len, s, n + 1u);
  b->len += n;
}

/* PREFIX, then the decimal digits of I. */
static void key_put_index(KeyText *b, const char *prefix, size_t i) {
  char digits[24];
  size_t at = sizeof digits - 1u;
  digits[at] = '\0';
  do {
    at--;
    digits[at] = (char)('0' + (int)(i % 10u));
    i /= 10u;
  } while (i > 0u && at > 0u);
  key_put(b, prefix);
  key_put(b, digits + at);
}

/* The text of the key argument form T (key_arg_form). An application
   goes in parentheses. */
static void key_put_type(KeyText *b, const Term *t) {
  if (t->kind == TERM_VAR) {
    key_put(b, t->name);
    return;
  }
  if (t->left->kind == TERM_VAR) {
    key_put(b, "(");
    key_put(b, t->left->name);
  } else {
    key_put(b, "(Prod ");
    key_put_type(b, t->left->right);
  }
  key_put(b, " ");
  key_put_type(b, t->right);
  key_put(b, ")");
}

/* The eq def of the type name NAME (Nat, Size, Flag) or the form head
   NAME (Option, List). */
static const char *key_eq_name(const char *name) {
  if (strcmp(name, "Nat") == 0)
    return "natEq";
  if (strcmp(name, "Size") == 0)
    return "sizeEq";
  if (strcmp(name, "Flag") == 0)
    return "flagEq";
  if (strcmp(name, "Option") == 0)
    return "optionEq";
  return "listEq";
}

/* The eq term of the key argument form T: Nat natEq, Size sizeEq, Flag
   flagEq, `Option T` (optionEq T eqT), `List T` (listEq T eqT) and
   `Prod A B` (prodEq A B eqA eqB). */
static void key_put_eq(KeyText *b, const Term *t) {
  if (t->kind == TERM_VAR) {
    key_put(b, key_eq_name(t->name));
    return;
  }
  if (t->left->kind == TERM_VAR) {
    key_put(b, "(");
    key_put(b, key_eq_name(t->left->name));
    key_put(b, " ");
    key_put_type(b, t->right);
    key_put(b, " ");
    key_put_eq(b, t->right);
    key_put(b, ")");
    return;
  }
  key_put(b, "(prodEq ");
  key_put_type(b, t->left->right);
  key_put(b, " ");
  key_put_type(b, t->right);
  key_put(b, " ");
  key_put_eq(b, t->left->right);
  key_put(b, " ");
  key_put_eq(b, t->right);
  key_put(b, ")");
}

/* The eq term of the field J: (EQ keyEqAJ keyEqBJ). */
static void key_put_field_eq(KeyText *b, const Term *type, size_t j) {
  key_put(b, "(");
  key_put_eq(b, type);
  key_put_index(b, " keyEqA", j);
  key_put_index(b, " keyEqB", j);
  key_put(b, ")");
}

/* The conjunction of the field eq terms from the Pi T (the field J) on:
   flagYes for no field, the term for one field, else flagIf. */
static void key_put_conj(KeyText *b, const Term *t, size_t j) {
  if (t == NULL || t->kind != TERM_PI) {
    key_put(b, "flagYes");
    return;
  }
  if (t->right == NULL || t->right->kind != TERM_PI) {
    key_put_field_eq(b, t->left, j);
    return;
  }
  key_put(b, "(flagIf ");
  key_put_field_eq(b, t->left, j);
  key_put(b, " ");
  key_put_conj(b, t->right, j + 1u);
  key_put(b, " flagNo)");
}

/* "fun (NAME1 : T1) ... (NAMEm : Tm) => " for the arguments of the key
   space type TYPE; nothing when m is 0. */
static void key_put_fun(KeyText *b, const char *name, const Term *type) {
  const Term *t;
  size_t m = 0;
  for (t = type; t != NULL && t->kind == TERM_PI; t = t->right) {
    m++;
    key_put(b, m == 1u ? "fun (" : " (");
    key_put_index(b, name, m);
    key_put(b, " : ");
    key_put_type(b, t->left);
    key_put(b, ")");
  }
  key_put(b, m == 0u ? "" : " => ");
}

static int key_space(const Decl *d) {
  return d->kind == DECL_KEYSPACE && d->origin == ORIGIN_PROGRAM;
}

/* The case of keyEq for the key space I: an elim on the second key, with
   the field conjunction on the diagonal and flagNo off it. */
static void key_put_case(KeyText *b, const DeclList *out, size_t first, size_t i) {
  size_t k;
  key_put_fun(b, "keyEqA", out->items[i].type);
  key_put(b, "elim (fun (keyEqU : Key) => Flag)");
  for (k = first; k < out->count; k++) {
    if (!key_space(&out->items[k]))
      continue;
    key_put(b, " (");
    key_put_fun(b, "keyEqB", out->items[k].type);
    if (k == i)
      key_put_conj(b, out->items[i].type, 1u);
    else
      key_put(b, "flagNo");
    key_put(b, ")");
  }
  key_put(b, " keyEqY");
}

/* With a key space in the program, put the key-eq prelude directly after
   the generated family Key, with the trusted origin ORIGIN_DOMAIN. With
   an argument type outside the six forms there is no prelude: check.c
   gives REFUSE_KEYSPACE at the key space. */
static int key_eq_after_key(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  KeyText b;
  size_t n = 0;
  int forms = 1;
  size_t i;
  for (i = first; i < out->count; i++) {
    const Term *t;
    if (!key_space(&out->items[i]))
      continue;
    n++;
    for (t = out->items[i].type; t != NULL && t->kind == TERM_PI; t = t->right)
      forms = forms && key_arg_form(t->left);
  }
  if (n == 0u || !forms)
    return 1;
  b.arena = arena;
  b.len = 0u;
  b.cap = 4096u;
  b.buf = arena_alloc(arena, b.cap);
  if (b.buf == NULL)
    return 0;
  b.buf[0] = '\0';
  b.ok = 1;
  key_put(&b, key_eq_source);
  key_put(&b, "def keyEq : Key -> Key -> Flag := fun (keyEqX : Key) (keyEqY : Key) => elim (fun (keyEqT : Key) => Flag)");
  for (i = first; i < out->count; i++) {
    if (!key_space(&out->items[i]))
      continue;
    key_put(&b, " (");
    key_put_case(&b, out, first, i);
    key_put(&b, ")");
  }
  key_put(&b, " keyEqX\n");
  return b.ok && splice_after(arena, first, KEY_AFTER, 1u, KEY_EQ_SOURCE_NAME, b.buf, b.len, out, diag);
}

/* The front end puts the Key family directly before the first keyspace
   declaration of the program, with the trusted origin ORIGIN_DOMAIN (rule
   R1 is for program families), so the key and step preludes find Key.
   The family shares the argument terms of the keyspace types. */
static int key_family(Arena *arena, size_t first, DeclList *out) {
  size_t at = out->count;
  size_t n = 0;
  size_t k = 0;
  size_t i;
  Ctor *ctors;
  Decl *items;
  Decl key;
  for (i = first; i < out->count; i++) {
    if (out->items[i].kind == DECL_KEYSPACE && out->items[i].origin == ORIGIN_PROGRAM) {
      at = n == 0u ? i : at;
      n++;
    }
  }
  if (n == 0u)
    return 1;
  ctors = arena_alloc(arena, n * sizeof *ctors);
  items = arena_alloc(arena, (out->count + 1u) * sizeof *items);
  if (ctors == NULL || items == NULL)
    return 0;
  for (i = at; i < out->count; i++) {
    const Decl *s = &out->items[i];
    const Term *t;
    Field *fields = NULL;
    size_t arity = 0;
    size_t j = 0;
    if (s->kind != DECL_KEYSPACE || s->origin != ORIGIN_PROGRAM)
      continue;
    for (t = s->type; t != NULL && t->kind == TERM_PI; t = t->right)
      arity++;
    if (arity > 0u) {
      fields = arena_alloc(arena, arity * sizeof *fields);
      if (fields == NULL)
        return 0;
    }
    for (t = s->type; t != NULL && t->kind == TERM_PI; t = t->right) {
      fields[j].name = key_field_name(arena, s->name, j + 1u);
      if (fields[j].name == NULL)
        return 0;
      fields[j].type = t->left;
      fields[j].line = s->line;
      fields[j].col = s->col;
      fields[j].history = 0;
      j++;
    }
    ctors[k].name = s->name;
    ctors[k].fields = fields;
    ctors[k].field_count = arity;
    ctors[k].result = NULL;
    ctors[k].boundary = NULL;
    ctors[k].line = s->line;
    ctors[k].col = s->col;
    k++;
  }
  memset(&key, 0, sizeof key);
  key.kind = DECL_FAMILY;
  key.origin = ORIGIN_DOMAIN;
  key.line = out->items[at].line;
  key.col = out->items[at].col;
  key.name = "Key";
  key.ctors = ctors;
  key.ctor_count = n;
  key.block_first = at;
  key.block_count = 1u;
  memcpy(items, out->items, at * sizeof *items);
  items[at] = key;
  memcpy(items + at + 1u, out->items + at, (out->count - at) * sizeof *items);
  out->items = items;
  out->count += 1u;
  out->cap = out->count;
  return 1;
}

/* The step defs (quotient-lang S5, USER rulings Q-S5-26 (a) and Q-S5-27
   (a)). For each program step `step Fam b := [item, ...]`, the front end
   puts the def `stepFam : Fam -> Eff` directly after the step, with the
   trusted origin ORIGIN_DOMAIN (the body names flagIf and step#let). The
   body is `fun (step#body : Fam) (step#s : State) => ITEMS`:
   - a get `x := K` is `(fun (x : Val) => REST) (step#s K)`;
   - a let `y := e` is `step#let e (fun y => REST)`, and the checker gives
     y its type (a let at `Maybe T` aborts);
   - a set `K := v` is `(fun (step#s : State) => REST) (fun (step#k : Key)
     => flagIf (keyEq step#k K) v (step#s step#k))`;
   - the end is `some step#s`.
   The lexer cannot make the generated names. Step locals and their free
   uses in item terms get fresh names, so they cannot capture the global
   names used in generated key and state terms. A program def with the
   name stepFam gives REFUSE_NAME. */
typedef struct {
  Arena *arena;
  int line;
  int col;
  int ok;
} StepBuild;

/* A new term node, or NULL (and ok 0) when an allocation failed before. */
static const Term *step_node(StepBuild *b, TermKind kind, const char *name, uint64_t nat, const Term *left, const Term *right) {
  Term *t = b->ok ? arena_alloc(b->arena, sizeof *t) : NULL;
  if (t == NULL) {
    b->ok = 0;
    return NULL;
  }
  t->kind = kind;
  t->line = b->line;
  t->col = b->col;
  t->name = name;
  t->nat = nat;
  t->left = left;
  t->right = right;
  return t;
}

static const Term *step_var(StepBuild *b, const char *name) {
  return step_node(b, TERM_VAR, name, 0u, NULL, NULL);
}

static const Term *step_app(StepBuild *b, const Term *f, const Term *a) {
  return step_node(b, TERM_APP, NULL, 0u, f, a);
}

/* `fun (name : type) => body`; a NULL type gives a bare binder. */
static const Term *step_lam(StepBuild *b, const char *name, const Term *type, const Term *body) {
  return step_node(b, TERM_LAM, name, 0u, type, body);
}

/* Step locals have names that the lexer cannot make. Generated key terms
   keep their global names and always project the original body. */
typedef struct StepLocal StepLocal;
struct StepLocal {
  const char *name;
  const char *fresh;
  const StepLocal *next;
};

/* Rename free uses of step locals in a user term. A binder inside the
   term masks the step local in its body, but not in its annotation. */
static const Term *step_term(StepBuild *b, const Term *t, const StepLocal *scope) {
  const StepLocal *local;
  const StepLocal *body_scope = scope;
  StepLocal mask;
  Term *copy;
  if (t == NULL || !b->ok)
    return NULL;
  copy = arena_alloc(b->arena, sizeof *copy);
  if (copy == NULL) {
    b->ok = 0;
    return NULL;
  }
  *copy = *t;
  switch (t->kind) {
  case TERM_VAR:
    for (local = scope; local != NULL; local = local->next) {
      if (t->name != NULL && strcmp(t->name, local->name) == 0) {
        copy->name = local->fresh;
        break;
      }
    }
    break;
  case TERM_LAM:
  case TERM_PI:
  case TERM_SIGMA:
    if (t->name != NULL) {
      mask.name = t->name;
      mask.fresh = t->name;
      mask.next = scope;
      body_scope = &mask;
    }
    break;
  case TERM_NAT:
  case TERM_APP:
  case TERM_UNIV:
  case TERM_PAPP:
  case TERM_INEG:
  case TERM_IMEET:
  case TERM_IJOIN:
  case TERM_SYSTEM:
  case TERM_BRANCH:
    break;
  }
  copy->left = step_term(b, t->left, scope);
  copy->right = step_term(b, t->right, body_scope);
  return copy;
}

/* A key pattern argument: `b.f` is `f b`. */
static const Term *step_key_arg(StepBuild *b, const PatArg *a) {
  switch (a->kind) {
  case PAT_ARG_FIELD:
    return step_app(b, step_var(b, a->name), step_var(b, "step#body"));
  case PAT_ARG_NAT:
    return step_node(b, TERM_NAT, NULL, a->nat, NULL, NULL);
  case PAT_ARG_NAME:
    return step_var(b, a->name);
  }
  b->ok = 0;
  return NULL;
}

/* A key pattern: the space applied to each argument. */
static const Term *step_key(StepBuild *b, const KeyPat *pat) {
  const Term *t = step_var(b, pat->space);
  size_t i;
  for (i = 0; i < pat->arg_count; i++)
    t = step_app(b, t, step_key_arg(b, &pat->args[i]));
  return t;
}

/* The item IT in front of the term REST of the next items. */
static const Term *step_item(StepBuild *b, const StepItem *it, const Term *rest) {
  b->line = it->line;
  b->col = it->col;
  switch (it->kind) {
  case STEP_GET:
    return step_app(b, step_lam(b, it->name, step_var(b, "Val"), rest), step_app(b, step_var(b, "step#s"), step_key(b, &it->pat)));
  case STEP_LET:
    return step_app(b, step_app(b, step_var(b, "step#let"), it->term), step_lam(b, it->name, NULL, rest));
  case STEP_SET:
    return step_app(b, step_lam(b, "step#s", step_var(b, "State"), rest),
                    step_lam(b, "step#k", step_var(b, "Key"),
                             step_app(b,
                                      step_app(b, step_app(b, step_var(b, "flagIf"), step_app(b, step_app(b, step_var(b, "keyEq"), step_var(b, "step#k")), step_key(b, &it->pat))), it->term),
                                      step_app(b, step_var(b, "step#s"), step_var(b, "step#k")))));
  }
  b->ok = 0;
  return NULL;
}

/* The def stepFam of the step S, at the list position AT. */
static int step_def(Arena *arena, const Decl *s, size_t at, Decl *def) {
  StepBuild b = {arena, 0, 0, 1};
  StepLocal body = {s->step->binder, "step#body", NULL};
  const StepLocal *scope = &body;
  StepLocal *locals = arena_alloc(arena, (s->step->item_count + 1u) * sizeof *locals);
  StepItem *items = arena_alloc(arena, (s->step->item_count + 1u) * sizeof *items);
  size_t len = strlen(s->name);
  char *name = arena_alloc(arena, len + 5u);
  const Term *rest;
  size_t i;
  if (name == NULL || locals == NULL || items == NULL)
    return 0;
  memcpy(name, "step", 4u);
  memcpy(name + 4u, s->name, len + 1u);
  b.line = s->line;
  b.col = s->col;
  for (i = 0; i < s->step->item_count; i++) {
    items[i] = s->step->items[i];
    items[i].term = step_term(&b, items[i].term, scope);
    if (items[i].kind != STEP_SET) {
      locals[i].name = items[i].name;
      locals[i].fresh = key_field_name(arena, "step#local", i + 1u);
      locals[i].next = scope;
      if (locals[i].fresh == NULL)
        return 0;
      scope = &locals[i];
      items[i].name = locals[i].fresh;
    }
  }
  rest = step_app(&b, step_var(&b, "some"), step_var(&b, "step#s"));
  for (i = s->step->item_count; i > 0u; i--)
    rest = step_item(&b, &items[i - 1u], rest);
  b.line = s->line;
  b.col = s->col;
  memset(def, 0, sizeof *def);
  def->kind = DECL_DEF;
  def->origin = ORIGIN_DOMAIN;
  def->line = s->line;
  def->col = s->col;
  def->name = name;
  def->type = step_node(&b, TERM_PI, NULL, 0u, step_var(&b, s->name), step_var(&b, "Eff"));
  def->body = step_lam(&b, "step#body", step_var(&b, s->name), step_lam(&b, "step#s", step_var(&b, "State"), rest));
  def->block_first = at;
  def->block_count = 1u;
  return b.ok;
}

static int program_step(const Decl *d) {
  return d->kind == DECL_STEP && d->origin == ORIGIN_PROGRAM && d->step != NULL;
}

/* Put the def of each program step from FIRST on directly after it. */
static int step_defs(Arena *arena, size_t first, DeclList *out) {
  size_t n = 0;
  size_t j = 0;
  size_t i;
  Decl *items;
  for (i = first; i < out->count; i++)
    n += program_step(&out->items[i]) ? 1u : 0u;
  if (n == 0u)
    return 1;
  items = arena_alloc(arena, (out->count + n) * sizeof *items);
  if (items == NULL)
    return 0;
  for (i = 0; i < out->count; i++) {
    int add = i >= first && program_step(&out->items[i]);
    items[j] = out->items[i];
    j++;
    if (add && !step_def(arena, &out->items[i], j, &items[j]))
      return 0;
    j += add ? 1u : 0u;
  }
  out->items = items;
  out->count = j;
  out->cap = j;
  return 1;
}

/* A program footprint family (S5, X17): a summand of Body. */
static int footprint_family(const Decl *d) {
  return d->kind == DECL_FAMILY && d->origin == ORIGIN_PROGRAM && d->footprint != NULL;
}

/* PREFIX and NAME in one new string. */
static const char *front_prefixed(Arena *arena, const char *prefix, const char *name) {
  size_t p = strlen(prefix);
  size_t len = strlen(name);
  char *s = arena_alloc(arena, p + len + 1u);
  if (s == NULL)
    return NULL;
  memcpy(s, prefix, p);
  memcpy(s + p, name, len + 1u);
  return s;
}

/* The Body family (quotient-lang S5, USER rulings Q-S5-6 (a), Q-S5-22 (a),
   Q-S5-28 (a) and Q-S5-30 (a)). With a footprint family in the program,
   Body is a family with one constructor for each program footprint
   family, in the order of the family declarations: the family Pay gives
   the constructor bodyPay with one Pay field (Pay#1, a name that the
   lexer cannot make). The Body Decl goes directly after the last program
   footprint family. */
static int body_family(Arena *arena, size_t first, DeclList *out) {
  size_t at = 0;
  size_t n = 0;
  size_t k = 0;
  size_t i;
  Ctor *ctors;
  Field *fields;
  Decl *items;
  Decl body;
  for (i = first; i < out->count; i++) {
    at = footprint_family(&out->items[i]) ? i + 1u : at;
    n += footprint_family(&out->items[i]) ? 1u : 0u;
  }
  if (n == 0u)
    return 1;
  ctors = arena_alloc(arena, n * sizeof *ctors);
  fields = arena_alloc(arena, n * sizeof *fields);
  items = arena_alloc(arena, (out->count + 1u) * sizeof *items);
  if (ctors == NULL || fields == NULL || items == NULL)
    return 0;
  for (i = first; i < at; i++) {
    const Decl *fam = &out->items[i];
    StepBuild b = {arena, 0, 0, 1};
    if (!footprint_family(fam))
      continue;
    b.line = fam->line;
    b.col = fam->col;
    fields[k].name = key_field_name(arena, fam->name, 1u);
    fields[k].type = step_var(&b, fam->name);
    fields[k].line = fam->line;
    fields[k].col = fam->col;
    fields[k].history = 0;
    ctors[k].name = front_prefixed(arena, "body", fam->name);
    ctors[k].fields = &fields[k];
    ctors[k].field_count = 1u;
    ctors[k].result = NULL;
    ctors[k].boundary = NULL;
    ctors[k].line = fam->line;
    ctors[k].col = fam->col;
    if (fields[k].name == NULL || ctors[k].name == NULL || !b.ok)
      return 0;
    k++;
  }
  memset(&body, 0, sizeof body);
  body.kind = DECL_FAMILY;
  body.origin = ORIGIN_DOMAIN;
  body.line = out->items[at - 1u].line;
  body.col = out->items[at - 1u].col;
  body.name = "Body";
  body.ctors = ctors;
  body.ctor_count = n;
  body.block_first = at;
  body.block_count = 1u;
  memcpy(items, out->items, at * sizeof *items);
  items[at] = body;
  memcpy(items + at + 1u, out->items + at, (out->count - at) * sizeof *items);
  out->items = items;
  out->count += 1u;
  out->cap = out->count;
  return 1;
}

/* 1 if a program step of the family FAM is at FIRST or after it. */
static int has_step(const DeclList *out, size_t first, const char *fam) {
  size_t i;
  for (i = first; i < out->count; i++) {
    if (program_step(&out->items[i]) && strcmp(out->items[i].name, fam) == 0)
      return 1;
  }
  return 0;
}

/* The step def (USER rulings Q-S5-22 (a), Q-S5-29 (a) and Q-S5-30 (a)):
   `step : Body -> Eff := fun (step#t : Body) => elim (fun (step#u : Body)
   => Eff) CASE1 ... CASEn step#t`, one case for each Body constructor, in
   order: `fun (step#f : Fam) => stepFam step#f`, or `fun (step#f : Fam)
   => just` for a footprint family with no step. The def goes directly
   after the last of Body, Eff and the step<Fam> defs. With no Eff (no
   step prelude: no Key or no Val) the front makes no step def. */
static int body_step(Arena *arena, size_t first, DeclList *out) {
  StepBuild b = {arena, 0, 0, 1};
  size_t last = 0;
  size_t i;
  int body = 0;
  int eff = 0;
  const Term *e;
  Decl *items;
  Decl def;
  for (i = first; i < out->count; i++) {
    const Decl *d = &out->items[i];
    int is_body = d->kind == DECL_FAMILY && d->origin == ORIGIN_DOMAIN && strcmp(d->name, "Body") == 0;
    int is_eff = d->kind == DECL_DEF && strcmp(d->name, "Eff") == 0;
    body |= is_body;
    eff |= is_eff;
    last = program_step(d) ? i + 1u : last;
    last = (is_body || is_eff) ? i : last;
  }
  if (!body || !eff)
    return 1;
  b.line = out->items[last].line;
  b.col = out->items[last].col;
  e = step_app(&b, step_var(&b, "elim"), step_lam(&b, "step#u", step_var(&b, "Body"), step_var(&b, "Eff")));
  for (i = first; i < out->count; i++) {
    const Decl *fam = &out->items[i];
    int has;
    const char *name;
    if (!footprint_family(fam))
      continue;
    has = has_step(out, first, fam->name);
    name = has ? front_prefixed(arena, "step", fam->name) : "just";
    if (name == NULL)
      return 0;
    e = step_app(&b, e, step_lam(&b, "step#f", step_var(&b, fam->name), has ? step_app(&b, step_var(&b, name), step_var(&b, "step#f")) : step_var(&b, name)));
  }
  e = step_app(&b, e, step_var(&b, "step#t"));
  items = arena_alloc(arena, (out->count + 1u) * sizeof *items);
  if (items == NULL)
    return 0;
  memset(&def, 0, sizeof def);
  def.kind = DECL_DEF;
  def.origin = ORIGIN_DOMAIN;
  def.line = b.line;
  def.col = b.col;
  def.name = "step";
  def.type = step_node(&b, TERM_PI, NULL, 0u, step_var(&b, "Body"), step_var(&b, "Eff"));
  def.body = step_lam(&b, "step#t", step_var(&b, "Body"), e);
  def.block_first = last + 1u;
  def.block_count = 1u;
  if (!b.ok)
    return 0;
  memcpy(items, out->items, (last + 1u) * sizeof *items);
  items[last + 1u] = def;
  memcpy(items + last + 2u, out->items + last + 1u, (out->count - last - 1u) * sizeof *items);
  out->items = items;
  out->count += 1u;
  out->cap = out->count;
  return 1;
}

int front_load(Arena *arena, const char *source, const char *text, size_t len, DeclList *out, Diag *diag) {
  size_t first;
  out->items = NULL;
  out->count = 0;
  out->cap = 0;
  if (!load_one(arena, "domain/domain.lang", ORIGIN_DOMAIN, (const char *)domain_source, domain_source_len, out, diag))
    return 0;
  first = out->count;
  return load_one(arena, source, ORIGIN_PROGRAM, text, len, out, diag)
      && key_family(arena, first, out)
      && key_eq_after_key(arena, first, out, diag)
      && value_after_asset(arena, first, out, diag)
      && key_after_key(arena, first, out, diag)
      && step_after_val(arena, first, out, diag)
      && step_defs(arena, first, out)
      && body_family(arena, first, out)
      && body_step(arena, first, out)
      && auth_after_witness(arena, first, out, diag)
      && agg_after_sig(arena, first, out, diag)
      && qc_after_signs(arena, first, out, diag);
}

int front_load_domain(Arena *arena, const char *source, const char *domain, const char *text, size_t len, DeclList *out, Diag *diag) {
  size_t first;
  out->items = NULL;
  out->count = 0;
  out->cap = 0;
  if (!load_one(arena, "domain/domain.lang", ORIGIN_DOMAIN, (const char *)domain_source, domain_source_len, out, diag)
      || !load_one(arena, source, ORIGIN_DOMAIN, domain, strlen(domain), out, diag))
    return 0;
  first = out->count;
  return load_one(arena, source, ORIGIN_PROGRAM, text, len, out, diag)
      && key_family(arena, first, out)
      && key_eq_after_key(arena, first, out, diag)
      && value_after_asset(arena, first, out, diag)
      && key_after_key(arena, first, out, diag)
      && step_after_val(arena, first, out, diag)
      && step_defs(arena, first, out)
      && body_family(arena, first, out)
      && body_step(arena, first, out)
      && auth_after_witness(arena, first, out, diag)
      && agg_after_sig(arena, first, out, diag)
      && qc_after_signs(arena, first, out, diag);
}
