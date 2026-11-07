#include <stdarg.h>
#include <stdio.h>
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
  TokenList toks;
  Decl *items;
  size_t at = first;
  size_t i;
  for (i = 0; i < count; i++) {
    size_t k = def_at(out, first, after[i]);
    if (k == out->count)
      return 1;
    at = k > at ? k : at;
  }
  /* Generated locals use dotted names that a program cannot bind. */
  if (!lex_internal(arena, source, text, len, &toks, diag)
      || !parse_source(arena, source, ORIGIN_DOMAIN, &toks, &kernel, diag))
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
  "def effRun : Eff -> State -> State := fun (f : Eff) (s : State) => option s (fun (t : State) => t) (f s)\n"
  /* effTrans is the double composite of three paths by one hcomp
     (Q-S6-28 (a)). effAssoc is by funext over State and the Maybe elim on
     f s (S6 u5b). Both are fixed text and proofs only. */
  "def effTrans : (a : Eff) -> (b : Eff) -> (c : Eff) -> (d : Eff) -> Path Eff a b -> Path Eff b c -> Path Eff c d -> Path Eff a d :=\n"
  "  fun (a : Eff) (b : Eff) (c : Eff) (d : Eff) (p : Path Eff a b) (q : Path Eff b c) (r : Path Eff c d) =>\n"
  "    fun (i : I) => hcomp Eff (~i \\/ i) (fun (k : I) => [ ~i -> p @ (~k), i -> r @ k ]) (q @ i)\n"
  "def effAssoc : (f : Eff) -> (g : Eff) -> (h : Eff) -> Path Eff (effSeq (effSeq f g) h) (effSeq f (effSeq g h)) :=\n"
  "  fun (f : Eff) (g : Eff) (h : Eff) => fun (i : I) => fun (s : State) =>\n"
  "    elim (fun (z : Maybe State) => Path (Maybe State) (bind (bind z (fun (t : State) => g t)) (fun (t : State) => h t)) (bind z (fun (t : State) => bind (g t) (fun (u : State) => h u))))\n"
  "      (fun (j : I) => none)\n"
  "      (fun (c : State) => fun (j : I) => bind (g c) (fun (u : State) => h u))\n"
  "      (f s) @ i\n";

static const char *const STEP_AFTER[] = {"Key", "Val"};

/* The step prelude goes directly after the last of the program defs Key
   and Val. */
static int step_after_val(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, STEP_AFTER, 2u, STEP_SOURCE_NAME, step_source, sizeof step_source - 1u, out, diag);
}

/* The set prelude (quotient-lang S6 unit 5a, USER rulings Q-S6-26 (a)
   and Q-S6-29 (a)). The fixed defs give isSet by kernel proofs, with no
   trust point. stableIsSet makes isSet A from a path map and its
   constancy (one hcomp); piIsSet, maybeIsSet, sizeIsSet and natIsSet
   use it. setAbsurd has the flagAbsurd form, so the set prelude does not
   need the key-eq prelude. The front end puts these defs directly after
   effRun, the last def of the step prelude. */
#define SET_SOURCE_NAME "kernel/set.lang"

static const char set_source[] =
  "def setAbsurd : (X : Type 0) -> (u : X) -> (v : X) -> Path Flag flagNo flagYes -> Path X u v := fun (X : Type 0) (u : X) (v : X) (h : Path Flag flagNo flagYes) => fun (i : I) => elim (fun (f : Flag) => X) v u (h @ i)\n"
  "def stableIsSet : (A : Type 0) -> (F : (a : A) -> (x : A) -> Path A a x -> Path A a x) -> ((a : A) -> (x : A) -> (p : Path A a x) -> (q : Path A a x) -> Path (Path A a x) (F a x p) (F a x q)) -> isSet A := fun (A : Type 0) (F : (a : A) -> (x : A) -> Path A a x -> Path A a x) (C : (a : A) -> (x : A) -> (p : Path A a x) -> (q : Path A a x) -> Path (Path A a x) (F a x p) (F a x q)) (a : A) (b : A) (p : Path A a b) (q : Path A a b) => fun (j : I) => fun (i : I) => hcomp A (~i \\/ i \\/ ~j \\/ j) (fun (k : I) => [ ~i -> F a a (fun (l : I) => a) @ k, i -> (C a b (fun (l : I) => p @ l) (fun (l : I) => q @ l) @ j) @ k, ~j -> F a (p @ i) (fun (l : I) => p @ (l /\\ i)) @ k, j -> F a (q @ i) (fun (l : I) => q @ (l /\\ i)) @ k ]) a\n"
  "def piIsSet : (A : Type 0) -> (B : Type 0) -> isSet B -> isSet (A -> B) := fun (A : Type 0) (B : Type 0) (sB : isSet B) (f : A -> B) (g : A -> B) (p : Path (A -> B) f g) (q : Path (A -> B) f g) => fun (i : I) => fun (j : I) => fun (x : A) => (sB (f x) (g x) (fun (k : I) => (p @ k) x) (fun (k : I) => (q @ k) x) @ i) @ j\n"
  "def maybeIsNone : (X : Type 0) -> Maybe X -> Flag := fun (X : Type 0) (y : Maybe X) => elim (fun (z : Maybe X) => Flag) flagYes (fun (c : X) => flagNo) y\n"
  "def maybeIsSome : (X : Type 0) -> Maybe X -> Flag := fun (X : Type 0) (y : Maybe X) => elim (fun (z : Maybe X) => Flag) flagNo (fun (c : X) => flagYes) y\n"
  "def maybeGet : (X : Type 0) -> X -> Maybe X -> X := fun (X : Type 0) (d : X) (y : Maybe X) => elim (fun (z : Maybe X) => X) d (fun (c : X) => c) y\n"
  "def maybeNorm : (X : Type 0) -> (u : Maybe X) -> (x : Maybe X) -> Path (Maybe X) u x -> Path (Maybe X) u x := fun (X : Type 0) (u : Maybe X) => elim (fun (v : Maybe X) => (x : Maybe X) -> Path (Maybe X) v x -> Path (Maybe X) v x) (fun (x : Maybe X) (p : Path (Maybe X) none x) => (elim (fun (y : Maybe X) => Path Flag flagNo (maybeIsSome X y) -> Path (Maybe X) none y) (fun (e : Path Flag flagNo flagNo) => fun (i : I) => none) (fun (c : X) => fun (e : Path Flag flagNo flagYes) => setAbsurd (Maybe X) none (some c) e) x) (fun (i : I) => maybeIsSome X (p @ i))) (fun (a : X) => fun (x : Maybe X) (p : Path (Maybe X) (some a) x) => (elim (fun (y : Maybe X) => Path Flag flagNo (maybeIsNone X y) -> Path X a (maybeGet X a y) -> Path (Maybe X) (some a) y) (fun (e : Path Flag flagNo flagYes) (r : Path X a a) => setAbsurd (Maybe X) (some a) none e) (fun (c : X) => fun (e : Path Flag flagNo flagNo) (r : Path X a c) => fun (i : I) => some (r @ i)) x) (fun (i : I) => maybeIsNone X (p @ i)) (fun (i : I) => maybeGet X a (p @ i))) u\n"
  "def maybeNormConst : (X : Type 0) -> isSet X -> (u : Maybe X) -> (x : Maybe X) -> (p : Path (Maybe X) u x) -> (q : Path (Maybe X) u x) -> Path (Path (Maybe X) u x) (maybeNorm X u x p) (maybeNorm X u x q) := fun (X : Type 0) (sX : isSet X) (u : Maybe X) => elim (fun (v : Maybe X) => (x : Maybe X) -> (p : Path (Maybe X) v x) -> (q : Path (Maybe X) v x) -> Path (Path (Maybe X) v x) (maybeNorm X v x p) (maybeNorm X v x q)) (fun (x : Maybe X) => elim (fun (y : Maybe X) => (p : Path (Maybe X) none y) -> (q : Path (Maybe X) none y) -> Path (Path (Maybe X) none y) (maybeNorm X none y p) (maybeNorm X none y q)) (fun (p : Path (Maybe X) none none) (q : Path (Maybe X) none none) => fun (j : I) => fun (i : I) => none) (fun (c : X) => fun (p : Path (Maybe X) none (some c)) (q : Path (Maybe X) none (some c)) => setAbsurd (Path (Maybe X) none (some c)) (maybeNorm X none (some c) p) (maybeNorm X none (some c) q) (fun (i : I) => maybeIsSome X (p @ i))) x) (fun (a : X) => fun (x : Maybe X) => elim (fun (y : Maybe X) => (p : Path (Maybe X) (some a) y) -> (q : Path (Maybe X) (some a) y) -> Path (Path (Maybe X) (some a) y) (maybeNorm X (some a) y p) (maybeNorm X (some a) y q)) (fun (p : Path (Maybe X) (some a) none) (q : Path (Maybe X) (some a) none) => setAbsurd (Path (Maybe X) (some a) none) (maybeNorm X (some a) none p) (maybeNorm X (some a) none q) (fun (i : I) => maybeIsNone X (p @ i))) (fun (c : X) => fun (p : Path (Maybe X) (some a) (some c)) (q : Path (Maybe X) (some a) (some c)) => fun (j : I) => fun (i : I) => some ((sX a c (fun (k : I) => maybeGet X a (p @ k)) (fun (k : I) => maybeGet X a (q @ k)) @ j) @ i)) x) u\n"
  "def maybeIsSet : (X : Type 0) -> isSet X -> isSet (Maybe X) := fun (X : Type 0) (sX : isSet X) => stableIsSet (Maybe X) (maybeNorm X) (maybeNormConst X sX)\n"
  "def sizeIsZero : Size -> Flag := fun (n : Size) => elim (fun (t : Size) => Flag) flagYes (fun (k : Size) (ih : Flag) => flagNo) n\n"
  "def sizeIsPos : Size -> Flag := fun (n : Size) => elim (fun (t : Size) => Flag) flagNo (fun (k : Size) (ih : Flag) => flagYes) n\n"
  "def sizeDec : Size -> Size := fun (n : Size) => elim (fun (t : Size) => Size) sz0 (fun (k : Size) (ih : Size) => k) n\n"
  "def sizeNorm : (a : Size) -> (x : Size) -> Path Size a x -> Path Size a x := fun (a : Size) => elim (fun (t : Size) => (x : Size) -> Path Size t x -> Path Size t x) (fun (x : Size) => elim (fun (y : Size) => Path Size sz0 y -> Path Size sz0 y) (fun (p : Path Size sz0 sz0) => fun (i : I) => sz0) (fun (n : Size) (ihy : Path Size sz0 n -> Path Size sz0 n) => fun (p : Path Size sz0 (szS n)) => setAbsurd Size sz0 (szS n) (fun (i : I) => sizeIsPos (p @ i))) x) (fun (m : Size) (ih : (x : Size) -> Path Size m x -> Path Size m x) => fun (x : Size) => elim (fun (y : Size) => Path Size (szS m) y -> Path Size (szS m) y) (fun (p : Path Size (szS m) sz0) => setAbsurd Size (szS m) sz0 (fun (i : I) => sizeIsZero (p @ i))) (fun (n : Size) (ihy : Path Size (szS m) n -> Path Size (szS m) n) => fun (p : Path Size (szS m) (szS n)) => fun (i : I) => szS ((ih n (fun (k : I) => sizeDec (p @ k))) @ i)) x) a\n"
  "def sizeNormConst : (a : Size) -> (x : Size) -> (p : Path Size a x) -> (q : Path Size a x) -> Path (Path Size a x) (sizeNorm a x p) (sizeNorm a x q) := fun (a : Size) => elim (fun (t : Size) => (x : Size) -> (p : Path Size t x) -> (q : Path Size t x) -> Path (Path Size t x) (sizeNorm t x p) (sizeNorm t x q)) (fun (x : Size) => elim (fun (y : Size) => (p : Path Size sz0 y) -> (q : Path Size sz0 y) -> Path (Path Size sz0 y) (sizeNorm sz0 y p) (sizeNorm sz0 y q)) (fun (p : Path Size sz0 sz0) (q : Path Size sz0 sz0) => fun (j : I) => fun (i : I) => sz0) (fun (n : Size) (ihy : (p : Path Size sz0 n) -> (q : Path Size sz0 n) -> Path (Path Size sz0 n) (sizeNorm sz0 n p) (sizeNorm sz0 n q)) => fun (p : Path Size sz0 (szS n)) (q : Path Size sz0 (szS n)) => setAbsurd (Path Size sz0 (szS n)) (sizeNorm sz0 (szS n) p) (sizeNorm sz0 (szS n) q) (fun (i : I) => sizeIsPos (p @ i))) x) (fun (m : Size) (ih : (x : Size) -> (p : Path Size m x) -> (q : Path Size m x) -> Path (Path Size m x) (sizeNorm m x p) (sizeNorm m x q)) => fun (x : Size) => elim (fun (y : Size) => (p : Path Size (szS m) y) -> (q : Path Size (szS m) y) -> Path (Path Size (szS m) y) (sizeNorm (szS m) y p) (sizeNorm (szS m) y q)) (fun (p : Path Size (szS m) sz0) (q : Path Size (szS m) sz0) => setAbsurd (Path Size (szS m) sz0) (sizeNorm (szS m) sz0 p) (sizeNorm (szS m) sz0 q) (fun (i : I) => sizeIsZero (p @ i))) (fun (n : Size) (ihy : (p : Path Size (szS m) n) -> (q : Path Size (szS m) n) -> Path (Path Size (szS m) n) (sizeNorm (szS m) n p) (sizeNorm (szS m) n q)) => fun (p : Path Size (szS m) (szS n)) (q : Path Size (szS m) (szS n)) => fun (j : I) => fun (i : I) => szS (((ih n (fun (k : I) => sizeDec (p @ k)) (fun (k : I) => sizeDec (q @ k))) @ j) @ i)) x) a\n"
  "def sizeIsSet : isSet Size := stableIsSet Size sizeNorm sizeNormConst\n"
  "def natIsZero : Nat -> Flag := fun (n : Nat) => elim (fun (t : Nat) => Flag) flagYes (fun (k : Nat) (ih : Flag) => flagNo) n\n"
  "def natIsPos : Nat -> Flag := fun (n : Nat) => elim (fun (t : Nat) => Flag) flagNo (fun (k : Nat) (ih : Flag) => flagYes) n\n"
  "def natPred : Nat -> Nat := fun (n : Nat) => elim (fun (t : Nat) => Nat) 0 (fun (k : Nat) (ih : Nat) => k) n\n"
  "def natNorm : (a : Nat) -> (x : Nat) -> Path Nat a x -> Path Nat a x := fun (a : Nat) => elim (fun (t : Nat) => (x : Nat) -> Path Nat t x -> Path Nat t x) (fun (x : Nat) => elim (fun (y : Nat) => Path Nat 0 y -> Path Nat 0 y) (fun (p : Path Nat 0 0) => fun (i : I) => 0) (fun (n : Nat) (ihy : Path Nat 0 n -> Path Nat 0 n) => fun (p : Path Nat 0 (natSucc n)) => setAbsurd Nat 0 (natSucc n) (fun (i : I) => natIsPos (p @ i))) x) (fun (m : Nat) (ih : (x : Nat) -> Path Nat m x -> Path Nat m x) => fun (x : Nat) => elim (fun (y : Nat) => Path Nat (natSucc m) y -> Path Nat (natSucc m) y) (fun (p : Path Nat (natSucc m) 0) => setAbsurd Nat (natSucc m) 0 (fun (i : I) => natIsZero (p @ i))) (fun (n : Nat) (ihy : Path Nat (natSucc m) n -> Path Nat (natSucc m) n) => fun (p : Path Nat (natSucc m) (natSucc n)) => fun (i : I) => natSucc ((ih n (fun (k : I) => natPred (p @ k))) @ i)) x) a\n"
  "def natNormConst : (a : Nat) -> (x : Nat) -> (p : Path Nat a x) -> (q : Path Nat a x) -> Path (Path Nat a x) (natNorm a x p) (natNorm a x q) := fun (a : Nat) => elim (fun (t : Nat) => (x : Nat) -> (p : Path Nat t x) -> (q : Path Nat t x) -> Path (Path Nat t x) (natNorm t x p) (natNorm t x q)) (fun (x : Nat) => elim (fun (y : Nat) => (p : Path Nat 0 y) -> (q : Path Nat 0 y) -> Path (Path Nat 0 y) (natNorm 0 y p) (natNorm 0 y q)) (fun (p : Path Nat 0 0) (q : Path Nat 0 0) => fun (j : I) => fun (i : I) => 0) (fun (n : Nat) (ihy : (p : Path Nat 0 n) -> (q : Path Nat 0 n) -> Path (Path Nat 0 n) (natNorm 0 n p) (natNorm 0 n q)) => fun (p : Path Nat 0 (natSucc n)) (q : Path Nat 0 (natSucc n)) => setAbsurd (Path Nat 0 (natSucc n)) (natNorm 0 (natSucc n) p) (natNorm 0 (natSucc n) q) (fun (i : I) => natIsPos (p @ i))) x) (fun (m : Nat) (ih : (x : Nat) -> (p : Path Nat m x) -> (q : Path Nat m x) -> Path (Path Nat m x) (natNorm m x p) (natNorm m x q)) => fun (x : Nat) => elim (fun (y : Nat) => (p : Path Nat (natSucc m) y) -> (q : Path Nat (natSucc m) y) -> Path (Path Nat (natSucc m) y) (natNorm (natSucc m) y p) (natNorm (natSucc m) y q)) (fun (p : Path Nat (natSucc m) 0) (q : Path Nat (natSucc m) 0) => setAbsurd (Path Nat (natSucc m) 0) (natNorm (natSucc m) 0 p) (natNorm (natSucc m) 0 q) (fun (i : I) => natIsZero (p @ i))) (fun (n : Nat) (ihy : (p : Path Nat (natSucc m) n) -> (q : Path Nat (natSucc m) n) -> Path (Path Nat (natSucc m) n) (natNorm (natSucc m) n p) (natNorm (natSucc m) n q)) => fun (p : Path Nat (natSucc m) (natSucc n)) (q : Path Nat (natSucc m) (natSucc n)) => fun (j : I) => fun (i : I) => natSucc (((ih n (fun (k : I) => natPred (p @ k)) (fun (k : I) => natPred (q @ k))) @ j) @ i)) x) a\n"
  "def natIsSet : isSet Nat := stableIsSet Nat natNorm natNormConst\n";

/* valIsSet is by the form of the program def Val: Size gives sizeIsSet
   and Nat gives natIsSet. With another form there is no valIsSet and no
   effIsSet (Q-S6-29 (a)). These defs go directly after natIsSet. */
static const char val_size_source[] =
  "def valIsSet : isSet Val := sizeIsSet\n"
  "def effIsSet : isSet Eff := piIsSet State (Maybe State) (maybeIsSet State (piIsSet Key Val valIsSet))\n";

static const char val_nat_source[] =
  "def valIsSet : isSet Val := natIsSet\n"
  "def effIsSet : isSet Eff := piIsSet State (Maybe State) (maybeIsSet State (piIsSet Key Val valIsSet))\n";

static const char *const SET_AFTER[] = {"effRun"};
static const char *const VAL_SET_AFTER[] = {"natIsSet"};

/* The form of the def Val in OUT from FIRST on: 1 for Size, 2 for Nat, 0
   for another form or no def Val. */
static int val_form(const DeclList *out, size_t first) {
  size_t k = def_at(out, first, "Val");
  const Term *t;
  if (k == out->count)
    return 0;
  t = out->items[k].body;
  if (t == NULL || t->kind != TERM_VAR || t->name == NULL)
    return 0;
  if (strcmp(t->name, "Size") == 0)
    return 1;
  return strcmp(t->name, "Nat") == 0 ? 2 : 0;
}

static int set_after_step(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  int form;
  if (!splice_after(arena, first, SET_AFTER, 1u, SET_SOURCE_NAME, set_source, sizeof set_source - 1u, out, diag))
    return 0;
  form = val_form(out, first);
  if (form == 1)
    return splice_after(arena, first, VAL_SET_AFTER, 1u, SET_SOURCE_NAME, val_size_source, sizeof val_size_source - 1u, out, diag);
  if (form == 2)
    return splice_after(arena, first, VAL_SET_AFTER, 1u, SET_SOURCE_NAME, val_nat_source, sizeof val_nat_source - 1u, out, diag);
  return 1;
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
  "def listEq : (A : Type 0) -> (A -> A -> Flag) -> List A -> List A -> Flag := fun (A : Type 0) (eqA : A -> A -> Flag) (xs : List A) (ys : List A) => (fun (un : List A -> Option (Prod A (List A))) => fold (fun (h : A) (r : List A -> Flag) (zs : List A) => option flagNo (fun (p : Prod A (List A)) => flagIf (eqA h (first p)) (r (second p)) flagNo) (un zs)) (fun (zs : List A) => option flagYes (fun (p : Prod A (List A)) => flagNo) (un zs)) xs ys) (fun (l : List A) => fold (fun (g : A) (acc : Option (Prod A (List A))) => some (pair g (option nil (fun (q : Prod A (List A)) => cons (first q) (second q)) acc))) none l)\n"
  "def flagAbsurd : (X : Type 0) -> (u : X) -> (v : X) -> Path Flag flagNo flagYes -> Path X u v := fun (X : Type 0) (u : X) (v : X) (h : Path Flag flagNo flagYes) => fun (i : I) => elim (fun (f : Flag) => X) v u (h @ i)\n"
  "def flagAndLeft : (p : Flag) -> (q : Flag) -> Path Flag (flagIf p q flagNo) flagYes -> Path Flag p flagYes := fun (p : Flag) (q : Flag) => elim (fun (t : Flag) => Path Flag (flagIf t q flagNo) flagYes -> Path Flag t flagYes) (fun (h : Path Flag (flagIf flagYes q flagNo) flagYes) => refl) (fun (h : Path Flag (flagIf flagNo q flagNo) flagYes) => flagAbsurd Flag flagNo flagYes h) p\n"
  "def flagAndRight : (p : Flag) -> (q : Flag) -> Path Flag (flagIf p q flagNo) flagYes -> Path Flag q flagYes := fun (p : Flag) (q : Flag) => elim (fun (t : Flag) => Path Flag (flagIf t q flagNo) flagYes -> Path Flag q flagYes) (fun (h : Path Flag (flagIf flagYes q flagNo) flagYes) => h) (fun (h : Path Flag (flagIf flagNo q flagNo) flagYes) => flagAbsurd Flag q flagYes h) p\n"
  "def flagEqSound : (a : Flag) -> (b : Flag) -> Path Flag (flagEq a b) flagYes -> Path Flag a b := fun (a : Flag) => elim (fun (s : Flag) => (b : Flag) -> Path Flag (flagEq s b) flagYes -> Path Flag s b) (fun (b : Flag) => elim (fun (t : Flag) => Path Flag (flagEq flagYes t) flagYes -> Path Flag flagYes t) (fun (h : Path Flag (flagEq flagYes flagYes) flagYes) => refl) (fun (h : Path Flag (flagEq flagYes flagNo) flagYes) => flagAbsurd Flag flagYes flagNo h) b) (fun (b : Flag) => elim (fun (t : Flag) => Path Flag (flagEq flagNo t) flagYes -> Path Flag flagNo t) (fun (h : Path Flag (flagEq flagNo flagYes) flagYes) => flagAbsurd Flag flagNo flagYes h) (fun (h : Path Flag (flagEq flagNo flagNo) flagYes) => refl) b) a\n"
  "def natEqSound : (a : Nat) -> (b : Nat) -> Path Flag (natEq a b) flagYes -> Path Nat a b := fun (a : Nat) => elim (fun (s : Nat) => (b : Nat) -> Path Flag (natEq s b) flagYes -> Path Nat s b) (fun (b : Nat) => elim (fun (t : Nat) => Path Flag (natEq 0 t) flagYes -> Path Nat 0 t) (fun (h : Path Flag (natEq 0 0) flagYes) => refl) (fun (j : Nat) (jh : Path Flag (natEq 0 j) flagYes -> Path Nat 0 j) (h : Path Flag (natEq 0 (natSucc j)) flagYes) => flagAbsurd Nat 0 (natSucc j) h) b) (fun (k : Nat) (ih : (b : Nat) -> Path Flag (natEq k b) flagYes -> Path Nat k b) (b : Nat) => elim (fun (t : Nat) => Path Flag (natEq (natSucc k) t) flagYes -> Path Nat (natSucc k) t) (fun (h : Path Flag (natEq (natSucc k) 0) flagYes) => flagAbsurd Nat (natSucc k) 0 h) (fun (j : Nat) (jh : Path Flag (natEq (natSucc k) j) flagYes -> Path Nat (natSucc k) j) (h : Path Flag (natEq (natSucc k) (natSucc j)) flagYes) => cong (fun (n : Nat) => natSucc n) (ih j h)) b) a\n"
  "def sizeEqSound : (a : Size) -> (b : Size) -> Path Flag (sizeEq a b) flagYes -> Path Size a b := fun (a : Size) => elim (fun (s : Size) => (b : Size) -> Path Flag (sizeEq s b) flagYes -> Path Size s b) (fun (b : Size) => elim (fun (t : Size) => Path Flag (sizeEq sz0 t) flagYes -> Path Size sz0 t) (fun (h : Path Flag (sizeEq sz0 sz0) flagYes) => refl) (fun (j : Size) (jh : Path Flag (sizeEq sz0 j) flagYes -> Path Size sz0 j) (h : Path Flag (sizeEq sz0 (szS j)) flagYes) => flagAbsurd Size sz0 (szS j) h) b) (fun (k : Size) (ih : (b : Size) -> Path Flag (sizeEq k b) flagYes -> Path Size k b) (b : Size) => elim (fun (t : Size) => Path Flag (sizeEq (szS k) t) flagYes -> Path Size (szS k) t) (fun (h : Path Flag (sizeEq (szS k) sz0) flagYes) => flagAbsurd Size (szS k) sz0 h) (fun (j : Size) (jh : Path Flag (sizeEq (szS k) j) flagYes -> Path Size (szS k) j) (h : Path Flag (sizeEq (szS k) (szS j)) flagYes) => cong (fun (n : Size) => szS n) (ih j h)) b) a\n"
  "def optionEqSound : (A : Type 0) -> (eqA : A -> A -> Flag) -> ((a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) -> (x : Option A) -> (y : Option A) -> Path Flag (optionEq A eqA x y) flagYes -> Path (Option A) x y := fun (A : Type 0) (eqA : A -> A -> Flag) (sA : (a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) (x : Option A) => elim (fun (s : Option A) => (y : Option A) -> Path Flag (optionEq A eqA s y) flagYes -> Path (Option A) s y) (fun (y : Option A) => elim (fun (t : Option A) => Path Flag (optionEq A eqA none t) flagYes -> Path (Option A) none t) (fun (h : Path Flag (optionEq A eqA none none) flagYes) => refl) (fun (b : A) (h : Path Flag (optionEq A eqA none (some b)) flagYes) => flagAbsurd (Option A) none (some b) h) y) (fun (a : A) (y : Option A) => elim (fun (t : Option A) => Path Flag (optionEq A eqA (some a) t) flagYes -> Path (Option A) (some a) t) (fun (h : Path Flag (optionEq A eqA (some a) none) flagYes) => flagAbsurd (Option A) (some a) none h) (fun (b : A) (h : Path Flag (optionEq A eqA (some a) (some b)) flagYes) => cong (fun (z : A) => some z) (sA a b h)) y) x\n"
  "def prodEqSound : (A : Type 0) -> (B : Type 0) -> (eqA : A -> A -> Flag) -> (eqB : B -> B -> Flag) -> ((a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) -> ((a : B) -> (b : B) -> Path Flag (eqB a b) flagYes -> Path B a b) -> (x : Prod A B) -> (y : Prod A B) -> Path Flag (prodEq A B eqA eqB x y) flagYes -> Path (Prod A B) x y := fun (A : Type 0) (B : Type 0) (eqA : A -> A -> Flag) (eqB : B -> B -> Flag) (sA : (a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) (sB : (a : B) -> (b : B) -> Path Flag (eqB a b) flagYes -> Path B a b) (x : Prod A B) => elim (fun (s : Prod A B) => (y : Prod A B) -> Path Flag (prodEq A B eqA eqB s y) flagYes -> Path (Prod A B) s y) (fun (a1 : A) (b1 : B) (y : Prod A B) => elim (fun (t : Prod A B) => Path Flag (prodEq A B eqA eqB (pair a1 b1) t) flagYes -> Path (Prod A B) (pair a1 b1) t) (fun (a2 : A) (b2 : B) (h : Path Flag (prodEq A B eqA eqB (pair a1 b1) (pair a2 b2)) flagYes) => fun (i : I) => pair ((sA a1 a2 (flagAndLeft (eqA a1 a2) (eqB b1 b2) h)) @ i) ((sB b1 b2 (flagAndRight (eqA a1 a2) (eqB b1 b2) h)) @ i)) y) x\n"
  "def listUncons : (A : Type 0) -> List A -> Option (Prod A (List A)) := fun (A : Type 0) (l : List A) => fold (fun (g : A) (acc : Option (Prod A (List A))) => some (pair g (option nil (fun (q : Prod A (List A)) => cons (first q) (second q)) acc))) none l\n"
  "def listRebuild : (A : Type 0) -> Option (Prod A (List A)) -> List A := fun (A : Type 0) (o : Option (Prod A (List A))) => option nil (fun (q : Prod A (List A)) => cons (first q) (second q)) o\n"
  "def listRound : (A : Type 0) -> (l : List A) -> Path (List A) (listRebuild A (listUncons A l)) l := fun (A : Type 0) (l : List A) => elim (fun (m : List A) => Path (List A) (listRebuild A (listUncons A m)) m) refl (fun (a : A) (m : List A) (ih : Path (List A) (listRebuild A (listUncons A m)) m) => fun (i : I) => cons a (ih @ i)) l\n"
  "def listEqSound : (A : Type 0) -> (eqA : A -> A -> Flag) -> ((a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) -> (xs : List A) -> (ys : List A) -> Path Flag (listEq A eqA xs ys) flagYes -> Path (List A) xs ys := fun (A : Type 0) (eqA : A -> A -> Flag) (sA : (a : A) -> (b : A) -> Path Flag (eqA a b) flagYes -> Path A a b) (xs : List A) => elim (fun (s : List A) => (ys : List A) -> Path Flag (listEq A eqA s ys) flagYes -> Path (List A) s ys) (fun (ys : List A) => elim (fun (t : List A) => Path Flag (listEq A eqA nil t) flagYes -> Path (List A) nil t) (fun (h : Path Flag (listEq A eqA nil nil) flagYes) => refl) (fun (b : A) (m : List A) (jh : Path Flag (listEq A eqA nil m) flagYes -> Path (List A) nil m) (h : Path Flag (listEq A eqA nil (cons b m)) flagYes) => flagAbsurd (List A) nil (cons b m) h) ys) (fun (a : A) (xs1 : List A) (ih : (ys : List A) -> Path Flag (listEq A eqA xs1 ys) flagYes -> Path (List A) xs1 ys) (ys : List A) => elim (fun (t : List A) => Path Flag (listEq A eqA (cons a xs1) t) flagYes -> Path (List A) (cons a xs1) t) (fun (h : Path Flag (listEq A eqA (cons a xs1) nil) flagYes) => flagAbsurd (List A) (cons a xs1) nil h) (fun (b : A) (ys1 : List A) (jh : Path Flag (listEq A eqA (cons a xs1) ys1) flagYes -> Path (List A) (cons a xs1) ys1) (h : Path Flag (listEq A eqA (cons a xs1) (cons b ys1)) flagYes) => fun (i : I) => cons ((sA a b (flagAndLeft (eqA a b) (listEq A eqA xs1 (listRebuild A (listUncons A ys1))) h)) @ i) ((transp (fun (j : I) => Path (List A) xs1 ((listRound A ys1) @ j)) i0 (ih (listRebuild A (listUncons A ys1)) (flagAndRight (eqA a b) (listEq A eqA xs1 (listRebuild A (listUncons A ys1))) h))) @ i)) ys) xs\n"
  "def flagAndIntro : (p : Flag) -> (q : Flag) -> Path Flag p flagYes -> Path Flag q flagYes -> Path Flag (flagIf p q flagNo) flagYes := fun (p : Flag) (q : Flag) => elim (fun (t : Flag) => Path Flag t flagYes -> Path Flag q flagYes -> Path Flag (flagIf t q flagNo) flagYes) (fun (hp : Path Flag flagYes flagYes) (hq : Path Flag q flagYes) => hq) (fun (hp : Path Flag flagNo flagYes) (hq : Path Flag q flagYes) => flagAbsurd Flag flagNo flagYes hp) p\n"
  "def flagEqRefl : (a : Flag) -> Path Flag (flagEq a a) flagYes := fun (a : Flag) => elim (fun (s : Flag) => Path Flag (flagEq s s) flagYes) refl refl a\n"
  "def natEqRefl : (a : Nat) -> Path Flag (natEq a a) flagYes := fun (a : Nat) => elim (fun (s : Nat) => Path Flag (natEq s s) flagYes) refl (fun (k : Nat) (ih : Path Flag (natEq k k) flagYes) => ih) a\n"
  "def sizeEqRefl : (a : Size) -> Path Flag (sizeEq a a) flagYes := fun (a : Size) => elim (fun (s : Size) => Path Flag (sizeEq s s) flagYes) refl (fun (k : Size) (ih : Path Flag (sizeEq k k) flagYes) => ih) a\n"
  "def optionEqRefl : (A : Type 0) -> (eqA : A -> A -> Flag) -> ((a : A) -> Path Flag (eqA a a) flagYes) -> (x : Option A) -> Path Flag (optionEq A eqA x x) flagYes := fun (A : Type 0) (eqA : A -> A -> Flag) (rA : (a : A) -> Path Flag (eqA a a) flagYes) (x : Option A) => elim (fun (s : Option A) => Path Flag (optionEq A eqA s s) flagYes) refl (fun (a : A) => rA a) x\n"
  "def prodEqRefl : (A : Type 0) -> (B : Type 0) -> (eqA : A -> A -> Flag) -> (eqB : B -> B -> Flag) -> ((a : A) -> Path Flag (eqA a a) flagYes) -> ((b : B) -> Path Flag (eqB b b) flagYes) -> (x : Prod A B) -> Path Flag (prodEq A B eqA eqB x x) flagYes := fun (A : Type 0) (B : Type 0) (eqA : A -> A -> Flag) (eqB : B -> B -> Flag) (rA : (a : A) -> Path Flag (eqA a a) flagYes) (rB : (b : B) -> Path Flag (eqB b b) flagYes) (x : Prod A B) => flagAndIntro (eqA (first x) (first x)) (eqB (second x) (second x)) (rA (first x)) (rB (second x))\n"
  "def listEqRefl : (A : Type 0) -> (eqA : A -> A -> Flag) -> ((a : A) -> Path Flag (eqA a a) flagYes) -> (xs : List A) -> Path Flag (listEq A eqA xs xs) flagYes := fun (A : Type 0) (eqA : A -> A -> Flag) (rA : (a : A) -> Path Flag (eqA a a) flagYes) (xs : List A) => elim (fun (s : List A) => Path Flag (listEq A eqA s s) flagYes) refl (fun (a : A) (m : List A) (ih : Path Flag (listEq A eqA m m) flagYes) => flagAndIntro (eqA a a) (listEq A eqA m (listRebuild A (listUncons A m))) (rA a) (transp (fun (j : I) => Path Flag (listEq A eqA m ((listRound A m) @ (~j))) flagYes) i0 ih)) xs\n";

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

/* The eq term of the field J: (EQ keyEqAJ SECONDJ). SECOND is " keyEq.B"
   for keyEq and " keyEq.A" for keyEqRefl (u4c1). */
static void key_put_field_eq_with(KeyText *b, const Term *type, size_t j, const char *second) {
  key_put(b, "(");
  key_put_eq(b, type);
  key_put_index(b, " keyEq.A", j);
  key_put_index(b, second, j);
  key_put(b, ")");
}

static void key_put_field_eq(KeyText *b, const Term *type, size_t j) {
  key_put_field_eq_with(b, type, j, " keyEq.B");
}

/* The conjunction of the field eq terms from the Pi T (the field J) on:
   flagYes for no field, the term for one field, else flagIf. */
static void key_put_conj_with(KeyText *b, const Term *t, size_t j, const char *second) {
  if (t == NULL || t->kind != TERM_PI) {
    key_put(b, "flagYes");
    return;
  }
  if (t->right == NULL || t->right->kind != TERM_PI) {
    key_put_field_eq_with(b, t->left, j, second);
    return;
  }
  key_put(b, "(flagIf ");
  key_put_field_eq_with(b, t->left, j, second);
  key_put(b, " ");
  key_put_conj_with(b, t->right, j + 1u, second);
  key_put(b, " flagNo)");
}

static void key_put_conj(KeyText *b, const Term *t, size_t j) {
  key_put_conj_with(b, t, j, " keyEq.B");
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
  key_put_fun(b, "keyEq.A", out->items[i].type);
  key_put(b, "elim (fun (keyEq.U : Key) => Flag)");
  for (k = first; k < out->count; k++) {
    if (!key_space(&out->items[k]))
      continue;
    key_put(b, " (");
    key_put_fun(b, "keyEq.B", out->items[k].type);
    if (k == i)
      key_put_conj(b, out->items[i].type, 1u);
    else
      key_put(b, "flagNo");
    key_put(b, ")");
  }
  key_put(b, " keyEq.Y");
}

/* u4b2 (Q-S6-17..19 (a)): the sound lemma for a key argument type, the
   mirror of key_put_eq: natEqSound, sizeEqSound, flagEqSound,
   (optionEqSound T eqT sT), (listEqSound T eqT sT) and
   (prodEqSound A B eqA eqB sA sB). */
static const char *key_sound_name(const char *name) {
  if (strcmp(name, "Nat") == 0)
    return "natEqSound";
  if (strcmp(name, "Size") == 0)
    return "sizeEqSound";
  if (strcmp(name, "Flag") == 0)
    return "flagEqSound";
  if (strcmp(name, "Option") == 0)
    return "optionEqSound";
  return "listEqSound";
}

static void key_put_sound(KeyText *b, const Term *t) {
  if (t->kind == TERM_VAR) {
    key_put(b, key_sound_name(t->name));
    return;
  }
  if (t->left->kind == TERM_VAR) {
    key_put(b, "(");
    key_put(b, key_sound_name(t->left->name));
    key_put(b, " ");
    key_put_type(b, t->right);
    key_put(b, " ");
    key_put_eq(b, t->right);
    key_put(b, " ");
    key_put_sound(b, t->right);
    key_put(b, ")");
    return;
  }
  key_put(b, "(prodEqSound ");
  key_put_type(b, t->left->right);
  key_put(b, " ");
  key_put_type(b, t->right);
  key_put(b, " ");
  key_put_eq(b, t->left->right);
  key_put(b, " ");
  key_put_eq(b, t->right);
  key_put(b, " ");
  key_put_sound(b, t->left->right);
  key_put(b, " ");
  key_put_sound(b, t->right);
  key_put(b, ")");
}

/* The key term (NAME P1 .. Pm) of a key space with the type TYPE and the
   field names PREFIX (with a leading space), or NAME when m is 0. */
static void key_put_key(KeyText *b, const char *name, const char *prefix, const Term *type) {
  const Term *t;
  size_t m = 0;
  if (type == NULL || type->kind != TERM_PI) {
    key_put(b, name);
    return;
  }
  key_put(b, "(");
  key_put(b, name);
  for (t = type; t != NULL && t->kind == TERM_PI; t = t->right) {
    m++;
    key_put_index(b, prefix, m);
  }
  key_put(b, ")");
}

/* The proof of Path Flag C_k flagYes, with C_k the conjunction from the
   field k: keyEq.H for k = 1, else flagAndRight on the proof for k - 1.
   HEAD is the type of the key space (the node of the field 1). */
static void key_put_rest(KeyText *b, const Term *head, size_t k) {
  const Term *t = head;
  size_t i;
  if (k <= 1u) {
    key_put(b, "keyEq.H");
    return;
  }
  for (i = 1u; i + 1u < k; i++)
    t = t->right;
  key_put(b, "(flagAndRight ");
  key_put_field_eq(b, t->left, k - 1u);
  key_put(b, " ");
  key_put_conj(b, t->right, k);
  key_put(b, " ");
  key_put_rest(b, head, k - 1u);
  key_put(b, ")");
}

/* The path on the diagonal: refl for no field, else a path lambda with
   the field paths (SOUND keyEqAj keyEqBj Hj) @ keyEq.I. Hj is flagAndLeft
   on the proof for the field j, the last field takes that proof. */
static void key_put_diag(KeyText *b, const char *name, const Term *type) {
  const Term *t;
  size_t j = 0;
  if (type == NULL || type->kind != TERM_PI) {
    key_put(b, "refl");
    return;
  }
  key_put(b, "fun (keyEq.I : I) => ");
  key_put(b, name);
  for (t = type; t != NULL && t->kind == TERM_PI; t = t->right) {
    j++;
    key_put(b, " ((");
    key_put_sound(b, t->left);
    key_put_index(b, " keyEq.A", j);
    key_put_index(b, " keyEq.B", j);
    key_put(b, " ");
    if (t->right != NULL && t->right->kind == TERM_PI) {
      key_put(b, "(flagAndLeft ");
      key_put_field_eq(b, t->left, j);
      key_put(b, " ");
      key_put_conj(b, t->right, j + 1u);
      key_put(b, " ");
      key_put_rest(b, type, j);
      key_put(b, ")");
    } else {
      key_put_rest(b, type, j);
    }
    key_put(b, ") @ keyEq.I)");
  }
}

/* The keyEqSound case for the key space i (the mirror of key_put_case):
   an elim on keyEq.Y, flagAbsurd off the diagonal, the field paths on it. */
static void key_put_sound_case(KeyText *b, const DeclList *out, size_t first, size_t i) {
  size_t k;
  const Decl *d = &out->items[i];
  key_put_fun(b, "keyEq.A", d->type);
  key_put(b, "fun (keyEq.Y : Key) => elim (fun (keyEq.U : Key) => Path Flag (keyEq ");
  key_put_key(b, d->name, " keyEq.A", d->type);
  key_put(b, " keyEq.U) flagYes -> Path Key ");
  key_put_key(b, d->name, " keyEq.A", d->type);
  key_put(b, " keyEq.U)");
  for (k = first; k < out->count; k++) {
    const Decl *e = &out->items[k];
    if (!key_space(e))
      continue;
    key_put(b, " (");
    key_put_fun(b, "keyEq.B", e->type);
    key_put(b, "fun (keyEq.H : Path Flag (keyEq ");
    key_put_key(b, d->name, " keyEq.A", d->type);
    key_put(b, " ");
    key_put_key(b, e->name, " keyEq.B", e->type);
    key_put(b, ") flagYes) => ");
    if (k == i) {
      key_put_diag(b, d->name, d->type);
    } else {
      key_put(b, "flagAbsurd Key ");
      key_put_key(b, d->name, " keyEq.A", d->type);
      key_put(b, " ");
      key_put_key(b, e->name, " keyEq.B", e->type);
      key_put(b, " keyEq.H");
    }
    key_put(b, ")");
  }
  key_put(b, " keyEq.Y");
}

/* u4c1 (Q-S6-24 (a)): the refl lemma for a key argument type, the
   mirror of key_put_sound: natEqRefl, sizeEqRefl, flagEqRefl,
   (optionEqRefl T eqT rT), (listEqRefl T eqT rT) and
   (prodEqRefl A B eqA eqB rA rB). */
static const char *key_refl_name(const char *name) {
  if (strcmp(name, "Nat") == 0)
    return "natEqRefl";
  if (strcmp(name, "Size") == 0)
    return "sizeEqRefl";
  if (strcmp(name, "Flag") == 0)
    return "flagEqRefl";
  if (strcmp(name, "Option") == 0)
    return "optionEqRefl";
  return "listEqRefl";
}

static void key_put_refl(KeyText *b, const Term *t) {
  if (t->kind == TERM_VAR) {
    key_put(b, key_refl_name(t->name));
    return;
  }
  if (t->left->kind == TERM_VAR) {
    key_put(b, "(");
    key_put(b, key_refl_name(t->left->name));
    key_put(b, " ");
    key_put_type(b, t->right);
    key_put(b, " ");
    key_put_eq(b, t->right);
    key_put(b, " ");
    key_put_refl(b, t->right);
    key_put(b, ")");
    return;
  }
  key_put(b, "(prodEqRefl ");
  key_put_type(b, t->left->right);
  key_put(b, " ");
  key_put_type(b, t->right);
  key_put(b, " ");
  key_put_eq(b, t->left->right);
  key_put(b, " ");
  key_put_eq(b, t->right);
  key_put(b, " ");
  key_put_refl(b, t->left->right);
  key_put(b, " ");
  key_put_refl(b, t->right);
  key_put(b, ")");
}

/* The refl proof of the field conjunction (key_put_conj with keyEq.A for
   both keys) from the Pi T (the field J) on: refl for no field,
   (REFL keyEqAJ) for one field, else flagAndIntro. */
static void key_put_refl_conj(KeyText *b, const Term *t, size_t j) {
  if (t == NULL || t->kind != TERM_PI) {
    key_put(b, "refl");
    return;
  }
  if (t->right == NULL || t->right->kind != TERM_PI) {
    key_put(b, "(");
    key_put_refl(b, t->left);
    key_put_index(b, " keyEq.A", j);
    key_put(b, ")");
    return;
  }
  key_put(b, "(flagAndIntro ");
  key_put_field_eq_with(b, t->left, j, " keyEq.A");
  key_put(b, " ");
  key_put_conj_with(b, t->right, j + 1u, " keyEq.A");
  key_put(b, " (");
  key_put_refl(b, t->left);
  key_put_index(b, " keyEq.A", j);
  key_put(b, ") ");
  key_put_refl_conj(b, t->right, j + 1u);
  key_put(b, ")");
}

/* The keyEqRefl case for the key space with the type TYPE. */
static void key_put_refl_case(KeyText *b, const Term *type) {
  key_put_fun(b, "keyEq.A", type);
  key_put_refl_conj(b, type, 1u);
}

/* The key-eq test: the program has a key space, and each key space
   argument is a key argument form. key_eq_after_key puts the key-eq
   prelude only then, and body_eq_after_body (S7 u5a1, Q-S7-12 (a)) makes
   bodyEq only then. */
static int key_eq_wanted(size_t first, const DeclList *out) {
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
  return n != 0u && forms;
}

/* With a key space in the program, put the key-eq prelude directly after
   the generated family Key, with the trusted origin ORIGIN_DOMAIN. With
   an argument type outside the six forms there is no prelude: check.c
   gives REFUSE_KEYSPACE at the key space. */
static int key_eq_after_key(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  KeyText b;
  size_t i;
  if (!key_eq_wanted(first, out))
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
  key_put(&b, "def keyEq : Key -> Key -> Flag := fun (keyEq.X : Key) (keyEq.Y : Key) => elim (fun (keyEq.T : Key) => Flag)");
  for (i = first; i < out->count; i++) {
    if (!key_space(&out->items[i]))
      continue;
    key_put(&b, " (");
    key_put_case(&b, out, first, i);
    key_put(&b, ")");
  }
  key_put(&b, " keyEq.X\n");
  key_put(&b, "def keyEqSound : (keyEq.X : Key) -> (keyEq.Y : Key) -> Path Flag (keyEq keyEq.X keyEq.Y) flagYes -> Path Key keyEq.X keyEq.Y := fun (keyEq.X : Key) => elim (fun (keyEq.T : Key) => (keyEq.Y : Key) -> Path Flag (keyEq keyEq.T keyEq.Y) flagYes -> Path Key keyEq.T keyEq.Y)");
  for (i = first; i < out->count; i++) {
    if (!key_space(&out->items[i]))
      continue;
    key_put(&b, " (");
    key_put_sound_case(&b, out, first, i);
    key_put(&b, ")");
  }
  key_put(&b, " keyEq.X\n");
  key_put(&b, "def keyEqRefl : (keyEq.X : Key) -> Path Flag (keyEq keyEq.X keyEq.X) flagYes := fun (keyEq.X : Key) => elim (fun (keyEq.T : Key) => Path Flag (keyEq keyEq.T keyEq.T) flagYes)");
  for (i = first; i < out->count; i++) {
    if (!key_space(&out->items[i]))
      continue;
    key_put(&b, " (");
    key_put_refl_case(&b, out->items[i].type);
    key_put(&b, ")");
  }
  key_put(&b, " keyEq.X\n");
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
  case TERM_APPEND:
  case TERM_SYSTEM:
  case TERM_BRANCH:
    break;
  }
  copy->left = step_term(b, t->left, scope);
  copy->right = step_term(b, t->right, body_scope);
  return copy;
}

/* A key pattern argument: `b.f` is `f VAR` (VAR is step#body in a step and
   ind#x or ind#y in an ind-if leaf). */
static const Term *step_key_arg(StepBuild *b, const PatArg *a, const char *var) {
  switch (a->kind) {
  case PAT_ARG_FIELD:
    return step_app(b, step_var(b, a->name), step_var(b, var));
  case PAT_ARG_NAT:
    return step_node(b, TERM_NAT, NULL, a->nat, NULL, NULL);
  case PAT_ARG_NAME:
    return step_var(b, a->name);
  }
  b->ok = 0;
  return NULL;
}

/* A key pattern: the space applied to each argument, the fields of VAR. */
static const Term *step_key_on(StepBuild *b, const KeyPat *pat, const char *var) {
  const Term *t = step_var(b, pat->space);
  size_t i;
  for (i = 0; i < pat->arg_count; i++)
    t = step_app(b, t, step_key_arg(b, &pat->args[i], var));
  return t;
}

/* A key pattern of a step: the fields of step#body. */
static const Term *step_key(StepBuild *b, const KeyPat *pat) {
  return step_key_on(b, pat, "step#body");
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

/* quotient-lang S7 u5a1 (USER rulings Q-S7-7 (a), Q-S7-11 (a) and
   Q-S7-12 (a)): bodyEq, the equality flag of Body (field by field, the
   mirror of keyEq), and bodyEqSound, its sound lemma (the mirror of
   keyEqSound). The front end puts them after the family Body and after
   the key-eq prelude, only when the key-eq prelude is in the program
   (key_eq_wanted) and each field of each program footprint family is a
   key argument form. Else it makes neither. */
#define BODY_EQ_SOURCE_NAME "kernel/body-eq.lang"
static const char *const BODY_AFTER[] = {"Body", "keyEqRefl"};

/* The field types of the footprint family FAM as a Pi chain (NULL for no
   field): the form of a key space type that the keyEq helpers take. */
static Term *body_chain(Arena *arena, const Decl *fam, int *ok) {
  Term *rest = NULL;
  size_t j;
  for (j = fam->ctors[0].field_count; j > 0u; j--) {
    Term *t = arena_alloc(arena, sizeof *t);
    if (t == NULL) {
      *ok = 0;
      return NULL;
    }
    memset(t, 0, sizeof *t);
    t->kind = TERM_PI;
    t->left = fam->ctors[0].fields[j - 1u].type;
    t->right = rest;
    rest = t;
  }
  return rest;
}

/* (bodyF VAR) for the footprint family F. */
static void body_put_var(KeyText *b, const Decl *fam, const char *var) {
  key_put(b, "(body");
  key_put(b, fam->name);
  key_put(b, " ");
  key_put(b, var);
  key_put(b, ")");
}

/* (bodyF (C P1 .. Pm)) for the footprint family F with the constructor C
   and the field names PREFIX (" keyEq.A" or " keyEq.B"). */
static void body_put_value(KeyText *b, const Decl *fam, const char *prefix, const Term *chain) {
  key_put(b, "(body");
  key_put(b, fam->name);
  key_put(b, " ");
  key_put_key(b, fam->ctors[0].name, prefix, chain);
  key_put(b, ")");
}

/* The Body path on the diagonal: refl for no field, else the path lambda
   of key_put_diag with bodyF on its body. */
static void body_put_diag(KeyText *b, const Decl *fam, const Term *chain) {
  static const char lam[] = "fun (keyEq.I : I) => ";
  size_t n = sizeof lam - 1u;
  KeyText d;
  if (chain == NULL) {
    key_put(b, "refl");
    return;
  }
  d.arena = b->arena;
  d.len = 0u;
  d.cap = 4096u;
  d.buf = arena_alloc(b->arena, d.cap);
  if (d.buf == NULL) {
    b->ok = 0;
    return;
  }
  d.buf[0] = '\0';
  d.ok = 1;
  key_put_diag(&d, fam->ctors[0].name, chain);
  if (!d.ok || d.len < n || d.len >= d.cap || memcmp(d.buf, lam, n) != 0) {
    b->ok = 0;
    return;
  }
  d.buf[d.len] = '\0';
  key_put(b, lam);
  key_put(b, "body");
  key_put(b, fam->name);
  key_put(b, " (");
  key_put(b, d.buf + n);
  key_put(b, ")");
}

/* The bodyEq case for the footprint family I: an elim on the second body;
   on the diagonal an elim on each footprint value and the field
   conjunction, off it flagNo. */
static void body_put_case(KeyText *b, const DeclList *out, Term *const *chain, size_t first, size_t i) {
  const Decl *f = &out->items[i];
  size_t k;
  key_put(b, "fun (bodyEq.P : ");
  key_put(b, f->name);
  key_put(b, ") => elim (fun (bodyEq.U : Body) => Flag)");
  for (k = first; k < out->count; k++) {
    const Decl *g = &out->items[k];
    if (!footprint_family(g))
      continue;
    key_put(b, " (fun (bodyEq.Q : ");
    key_put(b, g->name);
    key_put(b, ") => ");
    if (k == i) {
      key_put(b, "elim (fun (bodyEq.V : ");
      key_put(b, f->name);
      key_put(b, ") => Flag) (");
      key_put_fun(b, "keyEq.A", chain[i]);
      key_put(b, "elim (fun (bodyEq.W : ");
      key_put(b, f->name);
      key_put(b, ") => Flag) (");
      key_put_fun(b, "keyEq.B", chain[i]);
      key_put_conj(b, chain[i], 1u);
      key_put(b, ") bodyEq.Q) bodyEq.P");
    } else {
      key_put(b, "flagNo");
    }
    key_put(b, ")");
  }
  key_put(b, " bodyEq.Y");
}

/* The bodyEqSound diagonal for the footprint family F: an elim on bodyEq.P
   with bodyEq.Q and the H arrow in the motive, then an elim on bodyEq.Q, and
   the field paths under bodyF; applied to bodyEq.Q and keyEq.H. */
static void body_put_sound_diag(KeyText *b, const Decl *f, const Term *chain) {
  key_put(b, "(elim (fun (bodyEq.V : ");
  key_put(b, f->name);
  key_put(b, ") => (bodyEq.Q : ");
  key_put(b, f->name);
  key_put(b, ") -> Path Flag (bodyEq ");
  body_put_var(b, f, "bodyEq.V");
  key_put(b, " ");
  body_put_var(b, f, "bodyEq.Q");
  key_put(b, ") flagYes -> Path Body ");
  body_put_var(b, f, "bodyEq.V");
  key_put(b, " ");
  body_put_var(b, f, "bodyEq.Q");
  key_put(b, ") (");
  key_put_fun(b, "keyEq.A", chain);
  key_put(b, "fun (bodyEq.Q : ");
  key_put(b, f->name);
  key_put(b, ") => elim (fun (bodyEq.W : ");
  key_put(b, f->name);
  key_put(b, ") => Path Flag (bodyEq ");
  body_put_value(b, f, " keyEq.A", chain);
  key_put(b, " ");
  body_put_var(b, f, "bodyEq.W");
  key_put(b, ") flagYes -> Path Body ");
  body_put_value(b, f, " keyEq.A", chain);
  key_put(b, " ");
  body_put_var(b, f, "bodyEq.W");
  key_put(b, ") (");
  key_put_fun(b, "keyEq.B", chain);
  key_put(b, "fun (keyEq.H : Path Flag (bodyEq ");
  body_put_value(b, f, " keyEq.A", chain);
  key_put(b, " ");
  body_put_value(b, f, " keyEq.B", chain);
  key_put(b, ") flagYes) => ");
  body_put_diag(b, f, chain);
  key_put(b, ") bodyEq.Q) bodyEq.P) bodyEq.Q keyEq.H");
}

/* The bodyEqSound case for the footprint family I (the mirror of
   key_put_sound_case): an elim on bodyEq.Y, flagAbsurd off the diagonal,
   body_put_sound_diag on it. */
static void body_put_sound_case(KeyText *b, const DeclList *out, Term *const *chain, size_t first, size_t i) {
  const Decl *f = &out->items[i];
  size_t k;
  key_put(b, "fun (bodyEq.P : ");
  key_put(b, f->name);
  key_put(b, ") => fun (bodyEq.Y : Body) => elim (fun (bodyEq.U : Body) => Path Flag (bodyEq ");
  body_put_var(b, f, "bodyEq.P");
  key_put(b, " bodyEq.U) flagYes -> Path Body ");
  body_put_var(b, f, "bodyEq.P");
  key_put(b, " bodyEq.U)");
  for (k = first; k < out->count; k++) {
    const Decl *g = &out->items[k];
    if (!footprint_family(g))
      continue;
    key_put(b, " (fun (bodyEq.Q : ");
    key_put(b, g->name);
    key_put(b, ") => fun (keyEq.H : Path Flag (bodyEq ");
    body_put_var(b, f, "bodyEq.P");
    key_put(b, " ");
    body_put_var(b, g, "bodyEq.Q");
    key_put(b, ") flagYes) => ");
    if (k == i) {
      body_put_sound_diag(b, f, chain[i]);
    } else {
      key_put(b, "flagAbsurd Body ");
      body_put_var(b, f, "bodyEq.P");
      key_put(b, " ");
      body_put_var(b, g, "bodyEq.Q");
      key_put(b, " keyEq.H");
    }
    key_put(b, ")");
  }
  key_put(b, " bodyEq.Y");
}

static int body_eq_after_body(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  KeyText b;
  Term **chain;
  size_t n = 0;
  int forms = 1;
  int ok = 1;
  size_t i;
  if (!key_eq_wanted(first, out))
    return 1;
  for (i = first; i < out->count; i++) {
    const Decl *d = &out->items[i];
    size_t j;
    if (!footprint_family(d))
      continue;
    n++;
    for (j = 0; j < d->ctors[0].field_count; j++)
      forms = forms && key_arg_form(d->ctors[0].fields[j].type);
  }
  if (n == 0u || !forms)
    return 1;
  chain = arena_alloc(arena, out->count * sizeof *chain);
  if (chain == NULL)
    return 0;
  for (i = 0; i < out->count; i++)
    chain[i] = i >= first && footprint_family(&out->items[i]) ? body_chain(arena, &out->items[i], &ok) : NULL;
  if (!ok)
    return 0;
  b.arena = arena;
  b.len = 0u;
  b.cap = 4096u;
  b.buf = arena_alloc(arena, b.cap);
  if (b.buf == NULL)
    return 0;
  b.buf[0] = '\0';
  b.ok = 1;
  key_put(&b, "def bodyEq : Body -> Body -> Flag := fun (bodyEq.X : Body) (bodyEq.Y : Body) => elim (fun (bodyEq.T : Body) => Flag)");
  for (i = first; i < out->count; i++) {
    if (!footprint_family(&out->items[i]))
      continue;
    key_put(&b, " (");
    body_put_case(&b, out, chain, first, i);
    key_put(&b, ")");
  }
  key_put(&b, " bodyEq.X\n");
  key_put(&b, "def bodyEqSound : (bodyEq.X : Body) -> (bodyEq.Y : Body) -> Path Flag (bodyEq bodyEq.X bodyEq.Y) flagYes -> Path Body bodyEq.X bodyEq.Y := fun (bodyEq.X : Body) => elim (fun (bodyEq.T : Body) => (bodyEq.Y : Body) -> Path Flag (bodyEq bodyEq.T bodyEq.Y) flagYes -> Path Body bodyEq.T bodyEq.Y)");
  for (i = first; i < out->count; i++) {
    if (!footprint_family(&out->items[i]))
      continue;
    key_put(&b, " (");
    body_put_sound_case(&b, out, chain, first, i);
    key_put(&b, ")");
  }
  key_put(&b, " bodyEq.X\n");
  return b.ok && splice_after(arena, first, BODY_AFTER, 2u, BODY_EQ_SOURCE_NAME, b.buf, b.len, out, diag);
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

/* The trace monoid (quotient-lang S6 u3, USER ruling Q-S6-10 (a)): a
   fixed family Trace over Body, not a domain family with a relation
   parameter (R1 refuses one). The interval fields have new names, so a
   program field i or j does not hit them (rule R4). The front end puts it and traceFold
   directly after the placeholder def ind, so traceSwap can take the
   proof that ind a b is flagYes. With no ind (no Body), it adds nothing. */
#define TRACE_SOURCE_NAME "kernel/trace.lang"

static const char *const TRACE_AFTER[] = {"ind"};

static const char trace_source[] =
  "family Trace := traceEps\n"
  "  | traceCons (consHead : Body) (consTail : Trace)\n"
  "  | traceSwap (swapA : Body) (swapB : Body) (swapTail : Trace) (swapInd : Path Flag (ind swapA swapB) flagYes) (swapI : I)\n"
  "    [ ~swapI -> traceCons swapA (traceCons swapB swapTail), swapI -> traceCons swapB (traceCons swapA swapTail) ]\n"
  "  | traceSquash (traceFrom : Trace) (traceTo : Trace) (traceLeft : Path Trace traceFrom traceTo) (traceRight : Path Trace traceFrom traceTo) (squashI : I) (squashJ : I)\n"
  "    [ ~squashI -> traceLeft @ squashJ, squashI -> traceRight @ squashJ, ~squashJ -> traceFrom, squashJ -> traceTo ]\n"
  "def traceFold : (M : Type 0) -> isSet M -> (e : M) -> (push : Body -> M -> M) -> ((a : Body) -> (b : Body) -> (m : M) -> Path Flag (ind a b) flagYes -> Path M (push a (push b m)) (push b (push a m))) -> Trace -> M :=\n"
  "  fun (M : Type 0) (s : isSet M) (e : M) (push : Body -> M -> M) (sw : (a : Body) -> (b : Body) -> (m : M) -> Path Flag (ind a b) flagYes -> Path M (push a (push b m)) (push b (push a m))) (t : Trace) =>\n"
  "    fold e (fun (a : Body) (m : M) => push a m)\n"
  "      (fun (a : Body) (b : Body) (m : M) (p : Path Flag (ind a b) flagYes) => fun (swapI : I) => sw a b m p @ swapI)\n"
  "      (fun (x : M) (y : M) (p : Path M x y) (q : Path M x y) => fun (squashI : I) => fun (squashJ : I) => (s x y p q @ squashI) @ squashJ) t\n"
  "def traceIsSet : isSet Trace := fun (x : Trace) (y : Trace) (p : Path Trace x y) (q : Path Trace x y) => fun (i : I) => fun (j : I) => traceSquash x y p q i j\n"
  "def traceOne : Body -> Trace := fun (a : Body) => traceCons a traceEps\n"
  "def traceAppend : Trace -> Trace -> Trace :=\n"
  "  fun (t : Trace) (u : Trace) => traceFold Trace traceIsSet u (fun (a : Body) (r : Trace) => traceCons a r)\n"
  "    (fun (a : Body) (b : Body) (r : Trace) (p : Path Flag (ind a b) flagYes) => fun (i : I) => traceSwap a b r p i) t\n";

static int trace_after_ind(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, TRACE_AFTER, 1u, TRACE_SOURCE_NAME, trace_source, sizeof trace_source - 1u, out, diag);
}

/* The Foata form (quotient-lang S7 u5a2, USER rulings Q-S7-4 (a), Q-S7-7
   (a) and Q-S7-13 (a)). foataPeel splits a list of bodies into a step and
   the rest. A body goes in the step when ind is flagYes for each earlier
   body of the list and this body. foata peels steps until the list is
   empty. The input list is the fuel: a step of a nonempty list holds its
   first body. The front end puts the two defs directly after traceAppend.
   With no ind (no Body), it adds nothing. foataNil and foataStepsNil are
   nil at a known type: a bare nil in pair or as an argument does not
   infer. */
#define FOATA_SOURCE_NAME "kernel/foata.lang"

static const char *const FOATA_AFTER[] = {"traceAppend"};

static const char foata_source[] =
  "def foataNil : List Body := nil\n"
  "def foataStepsNil : List (List Body) := nil\n"
  "def foataPeel : List Body -> Prod (List Body) (List Body) := fun (w : List Body) => fold (fun (h : Body) (r : List Body -> Prod (List Body) (List Body)) (seen : List Body) => (fun (p : Prod (List Body) (List Body)) => elim (fun (f : Flag) => Prod (List Body) (List Body)) (pair (cons h (first p)) (second p)) (pair (first p) (cons h (second p))) (fold (fun (s : Body) (acc : Flag) => flagIf (ind s h) acc flagNo) flagYes seen)) (r (cons h seen))) (fun (seen : List Body) => pair foataNil foataNil) w foataNil\n"
  "def foata : List Body -> List (List Body) := fun (w : List Body) => fold (fun (h : Body) (r : List Body -> List (List Body)) (v : List Body) => (fun (p : Prod (List Body) (List Body)) => elim (fun (f : Flag) => List (List Body)) foataStepsNil (cons (first p) (r (second p))) (fold (fun (s : Body) (acc : Flag) => flagNo) flagYes v)) (foataPeel v)) (fun (v : List Body) => foataStepsNil) w w\n";

static int foata_after_trace(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, FOATA_AFTER, 1u, FOATA_SOURCE_NAME, foata_source, sizeof foata_source - 1u, out, diag);
}

/* The step test of the Foata form (quotient-lang S7 u5a2, USER ruling
   Q-S7-13 (a)). foataRemove removes the first body of a list that is equal
   to a body by bodyEq. foataStepEq is bag equality of two steps. foataEq
   is flagYes when the two Foata forms have equal steps in the same order.
   traceRemove removes the first body of a list that is equal to a body
   and is ind of each earlier body of the list (S7 u5b, USER ruling
   Q-S7-14 (a)). traceResidual walks the first list in order: a body is
   common when it is ind of each earlier body of the first residual and
   traceRemove removes it from the second list. traceLe is flagYes when
   the first residual is empty. compatible is flagYes when each body of
   the first residual is ind of each body of the second residual.
   The front end puts the defs after the later of foata and bodyEqSound.
   With no bodyEq, it adds nothing. foataNone is none at a known type. */
#define FOATA_EQ_SOURCE_NAME "kernel/foata-eq.lang"

static const char *const FOATA_EQ_AFTER[] = {"foata", "bodyEqSound"};

static const char foata_eq_source[] =
  "def foataNone : Option (List Body) := none\n"
  "def foataRemove : Body -> List Body -> Prod (List Body) (Option (List Body)) := fun (a : Body) (l : List Body) => fold (fun (h : Body) (acc : Prod (List Body) (Option (List Body))) => pair (cons h (first acc)) (elim (fun (f : Flag) => Option (List Body)) (some (first acc)) (option foataNone (fun (m : List Body) => some (cons h m)) (second acc)) (bodyEq a h))) (pair foataNil foataNone) l\n"
  "def foataStepEq : List Body -> List Body -> Flag := fun (x : List Body) (y : List Body) => option flagNo (fun (m : List Body) => fold (fun (s : Body) (acc : Flag) => flagNo) flagYes m) (fold (fun (h : Body) (r : List Body -> Option (List Body)) (ys : List Body) => option foataNone r (second (foataRemove h ys))) (fun (ys : List Body) => some ys) x y)\n"
  "def foataEq : List Body -> List Body -> Flag := fun (x : List Body) (y : List Body) => listEq (List Body) foataStepEq (foata x) (foata y)\n"
  "def traceRemove : Body -> List Body -> Prod Flag (List Body) := fun (a : Body) (l : List Body) => fold (fun (b : Body) (r : List Body -> Flag -> Prod Flag (List Body)) (seen : List Body) (done : Flag) => (fun (hit : Flag) => (fun (p : Prod Flag (List Body)) => elim (fun (f : Flag) => Prod Flag (List Body)) (pair flagYes (second p)) (pair (first p) (cons b (second p))) hit) (r (cons b seen) (flagIf hit flagYes done))) (flagIf done flagNo (flagIf (bodyEq a b) (fold (fun (s : Body) (acc : Flag) => flagIf (ind s b) acc flagNo) flagYes seen) flagNo))) (fun (seen : List Body) (done : Flag) => pair flagNo foataNil) l foataNil flagNo\n"
  "def traceResidual : List Body -> List Body -> Prod (List Body) (List Body) := fun (x : List Body) (y : List Body) => fold (fun (h : Body) (r : List Body -> List Body -> Prod (List Body) (List Body)) (ys : List Body) (xs : List Body) => (fun (p : Prod Flag (List Body)) => (fun (common : Flag) => (fun (q : Prod (List Body) (List Body)) => elim (fun (f : Flag) => Prod (List Body) (List Body)) q (pair (cons h (first q)) (second q)) common) (r (elim (fun (f : Flag) => List Body) (second p) ys common) (elim (fun (f : Flag) => List Body) xs (cons h xs) common))) (flagIf (fold (fun (s : Body) (acc : Flag) => flagIf (ind s h) acc flagNo) flagYes xs) (first p) flagNo)) (traceRemove h ys)) (fun (ys : List Body) (xs : List Body) => pair foataNil ys) x y foataNil\n"
  "def traceLe : List Body -> List Body -> Flag := fun (x : List Body) (y : List Body) => fold (fun (s : Body) (acc : Flag) => flagNo) flagYes (first (traceResidual x y))\n"
  "def compatible : List Body -> List Body -> Flag := fun (x : List Body) (y : List Body) => (fun (p : Prod (List Body) (List Body)) => fold (fun (a : Body) (acc : Flag) => flagIf (fold (fun (b : Body) (accB : Flag) => flagIf (ind a b) accB flagNo) flagYes (second p)) acc flagNo) flagYes (first p)) (traceResidual x y)\n";

static int foata_eq_after_foata(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, FOATA_EQ_AFTER, 2u, FOATA_EQ_SOURCE_NAME, foata_eq_source, sizeof foata_eq_source - 1u, out, diag);
}

/* The def ind (quotient-lang S6, USER ruling Q-S6-11 (a)) is a
   placeholder here: the type Body -> Body -> Flag and no body. The Ind
   matrix is check-time, so check.c makes the body at this def
   (front_ind_body). The def goes directly after the def step; with no def
   step (no Eff), directly after the family Body. No Body, no def.
   Directly after ind, the front puts the generated def D (quotient-lang
   S6 u8, USER ruling Q-S6-7 (a)), the negation of ind: `D : Body -> Body
   -> Flag := fun (dep#a : Body) (dep#b : Body) => flagIf (ind dep#a
   dep#b) flagNo flagYes`. The binders have the prefix dep#, so a program
   name does not hit them. */
static int ind_placeholder(Arena *arena, size_t first, DeclList *out) {
  StepBuild b = {arena, 0, 0, 1};
  size_t at = out->count;
  size_t i;
  Decl *items;
  Decl def;
  Decl dep;
  for (i = first; i < out->count; i++) {
    const Decl *d = &out->items[i];
    int is_body = d->kind == DECL_FAMILY && d->origin == ORIGIN_DOMAIN && strcmp(d->name, "Body") == 0;
    int is_step = d->kind == DECL_DEF && d->origin == ORIGIN_DOMAIN && strcmp(d->name, "step") == 0;
    at = (is_body || is_step) ? i : at;
  }
  if (at == out->count)
    return 1;
  b.line = out->items[at].line;
  b.col = out->items[at].col;
  items = arena_alloc(arena, (out->count + 2u) * sizeof *items);
  if (items == NULL)
    return 0;
  memset(&def, 0, sizeof def);
  def.kind = DECL_DEF;
  def.origin = ORIGIN_DOMAIN;
  def.line = b.line;
  def.col = b.col;
  def.name = "ind";
  def.type = step_node(&b, TERM_PI, NULL, 0u, step_var(&b, "Body"), step_node(&b, TERM_PI, NULL, 0u, step_var(&b, "Body"), step_var(&b, "Flag")));
  def.body = NULL;
  def.block_first = at + 1u;
  def.block_count = 1u;
  dep = def;
  dep.name = "D";
  dep.type = step_node(&b, TERM_PI, NULL, 0u, step_var(&b, "Body"), step_node(&b, TERM_PI, NULL, 0u, step_var(&b, "Body"), step_var(&b, "Flag")));
  dep.body = step_lam(&b, "dep#a", step_var(&b, "Body"), step_lam(&b, "dep#b", step_var(&b, "Body"), step_app(&b, step_app(&b, step_app(&b, step_var(&b, "flagIf"), step_app(&b, step_app(&b, step_var(&b, "ind"), step_var(&b, "dep#a")), step_var(&b, "dep#b"))), step_var(&b, "flagNo")), step_var(&b, "flagYes"))));
  dep.block_first = at + 2u;
  if (!b.ok)
    return 0;
  memcpy(items, out->items, (at + 1u) * sizeof *items);
  items[at + 1u] = def;
  items[at + 2u] = dep;
  memcpy(items + at + 3u, out->items + at + 1u, (out->count - at - 1u) * sizeof *items);
  out->items = items;
  out->count += 2u;
  out->cap = out->count;
  return 1;
}

/* The generated def commute (quotient-lang S6 u4a, USER rulings Q-S6-3
   (b), Q-S6-8 (a) and Q-S6-12 (b)): `commute : (a : Body) -> (b : Body)
   -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (step a) (step b))
   (effSeq (step b) (step a))`, a nested elim on a and b in the body_step
   order. The leaf at each pair (F, G) is a def com#leafN, so the checker
   can give REFUSE_COMMUTE at the first pair that fails. With no program
   slot def commute<F><G>, the leaf is `fun (com#h : Path Flag (ind A B)
   flagYes) => cong (fun (com#k : Flag) => flagIf com#k Y X) com#h` (X =
   effSeq (step A) (step B), Y = effSeq (step B) (step A)); it checks only
   when ind A B is flagNo or X and Y convert. With the slot, a def
   com#slotN checks the slot type and the leaf is `funExt (com#slotN com#f
   com#g)`. The front makes the text with the binder prefix com., parses
   it with lex_internal and changes com. to com#. A program name cannot
   contain a dot, so it cannot hit a binder or be changed by the rewrite.
   The defs go directly after the last of traceFold and the slot defs.
   With no Body, Eff, step or traceFold, the front adds nothing. */
#define COMMUTE_SOURCE_NAME "kernel/commute.lang"

typedef struct {
  char *s;
  size_t len;
  size_t cap;
  int ok;
} ComText;

static void com_put(ComText *t, const char *fmt, ...) {
  va_list args;
  int n;
  if (!t->ok)
    return;
  va_start(args, fmt);
  n = vsnprintf(t->s + t->len, t->cap - t->len, fmt, args);
  va_end(args);
  t->ok = n >= 0 && (size_t)n < t->cap - t->len;
  t->len += t->ok ? (size_t)n : 0u;
}

/* NAME with the prefix com. changed to com#; other names stay. */
static const char *com_name(Arena *arena, const char *name, int *ok) {
  const char *r;
  if (name == NULL || strncmp(name, "com.", 4u) != 0)
    return name;
  r = front_prefixed(arena, "com#", name + 4);
  *ok = *ok && r != NULL;
  return r != NULL ? r : name;
}

/* A copy of T with each com. name changed to com#. */
static const Term *com_term(Arena *arena, const Term *t, int *ok) {
  Term *n;
  if (t == NULL || !*ok)
    return t;
  n = arena_alloc(arena, sizeof *n);
  if (n == NULL) {
    *ok = 0;
    return t;
  }
  *n = *t;
  n->name = com_name(arena, t->name, ok);
  n->left = com_term(arena, t->left, ok);
  n->right = com_term(arena, t->right, ok);
  return n;
}

/* The index of the program def NAME at FIRST or after it, or OUT->count. */
static size_t program_def_at(const DeclList *out, size_t first, const char *name) {
  size_t at;
  for (at = first; at < out->count && !(out->items[at].kind == DECL_DEF && out->items[at].origin == ORIGIN_PROGRAM && strcmp(out->items[at].name, name) == 0); at++)
    ;
  return at;
}

/* The program slot def commute<F><G>, or NULL when it is out of memory. */
static const char *com_slot(Arena *arena, const char *f, const char *g) {
  const char *pre = front_prefixed(arena, "commute", f);
  return pre != NULL ? front_prefixed(arena, pre, g) : NULL;
}

static int body_commute(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  ComText t = {NULL, 0u, 0u, 1};
  DeclList kernel = {NULL, 0, 0};
  TokenList toks;
  size_t last = def_at(out, first, "traceFold");
  size_t set = def_at(out, first, "effIsSet");
  size_t fams = 0;
  size_t names = 0;
  size_t leaf = 0;
  size_t i;
  size_t j;
  int ok = 1;
  Decl *items;
  if (last == out->count || def_at(out, first, "Body") == out->count || def_at(out, first, "Eff") == out->count || def_at(out, first, "step") == out->count)
    return 1;
  for (i = first; i < out->count; i++) {
    fams += footprint_family(&out->items[i]) ? 1u : 0u;
    names += footprint_family(&out->items[i]) ? strlen(out->items[i].name) : 0u;
  }
  t.cap = 16384u + fams * fams * (2048u + 64u * names);
  t.s = arena_alloc(arena, t.cap);
  if (t.s == NULL)
    return 0;
  for (i = first; i < out->count; i++) {
    for (j = first; j < out->count; j++) {
      const char *f = out->items[i].name;
      const char *g = out->items[j].name;
      const char *slot;
      size_t at;
      if (!footprint_family(&out->items[i]) || !footprint_family(&out->items[j]))
        continue;
      slot = com_slot(arena, f, g);
      if (slot == NULL)
        return 0;
      at = program_def_at(out, first, slot);
      last = at != out->count && at > last ? at : last;
      if (at != out->count)
        com_put(&t, "def com.slot%zu : (com.f : %s) -> (com.g : %s) -> (com.s : State) -> Path (Maybe State) (effSeq (step (body%s com.f)) (step (body%s com.g)) com.s) (effSeq (step (body%s com.g)) (step (body%s com.f)) com.s) := %s\n", leaf, f, g, f, g, g, f, slot);
      com_put(&t, "def com.leaf%zu : (com.f : %s) -> (com.g : %s) -> Path Flag (ind (body%s com.f) (body%s com.g)) flagYes -> Path Eff (effSeq (step (body%s com.f)) (step (body%s com.g))) (effSeq (step (body%s com.g)) (step (body%s com.f))) :=\n", leaf, f, g, f, g, f, g, g, f);
      com_put(&t, "  fun (com.f : %s) (com.g : %s) (com.h : Path Flag (ind (body%s com.f) (body%s com.g)) flagYes) => ", f, g, f, g);
      if (at != out->count)
        com_put(&t, "funExt (com.slot%zu com.f com.g)\n", leaf);
      else
        com_put(&t, "cong (fun (com.k : Flag) => flagIf com.k (effSeq (step (body%s com.g)) (step (body%s com.f))) (effSeq (step (body%s com.f)) (step (body%s com.g)))) com.h\n", g, f, f, g);
      leaf++;
    }
  }
  com_put(&t, "def commute : (com.a : Body) -> (com.b : Body) -> Path Flag (ind com.a com.b) flagYes -> Path Eff (effSeq (step com.a) (step com.b)) (effSeq (step com.b) (step com.a)) :=\n");
  com_put(&t, "  fun (com.a : Body) => elim (fun (com.u : Body) => (com.b : Body) -> Path Flag (ind com.u com.b) flagYes -> Path Eff (effSeq (step com.u) (step com.b)) (effSeq (step com.b) (step com.u)))");
  leaf = 0;
  for (i = first; i < out->count; i++) {
    const char *f = out->items[i].name;
    if (!footprint_family(&out->items[i]))
      continue;
    com_put(&t, "\n    (fun (com.f : %s) (com.b : Body) => elim (fun (com.v : Body) => Path Flag (ind (body%s com.f) com.v) flagYes -> Path Eff (effSeq (step (body%s com.f)) (step com.v)) (effSeq (step com.v) (step (body%s com.f))))", f, f, f, f);
    for (j = first; j < out->count; j++) {
      if (!footprint_family(&out->items[j]))
        continue;
      com_put(&t, " (fun (com.g : %s) => com.leaf%zu com.f com.g)", out->items[j].name, leaf);
      leaf++;
    }
    com_put(&t, " com.b)");
  }
  com_put(&t, "\n    com.a\n");
  /* effSwap (Q-S6-28 (a)): two independent letters commute in front of a
     tail m. traceEval (Q-S6-29 (a)) only with a def effIsSet; then the
     text goes after the later of traceFold and effIsSet. evalAppend
     (Q-S6-27 (a)) and its two prop lemmas go with traceEval, also after
     traceAppend. */
  com_put(&t, "def effSwap : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (step a) (effSeq (step b) m)) (effSeq (step b) (effSeq (step a) m)) :=\n");
  com_put(&t, "  fun (a : Body) (b : Body) (m : Eff) (p : Path Flag (ind a b) flagYes) =>\n");
  com_put(&t, "    effTrans (effSeq (step a) (effSeq (step b) m)) (effSeq (effSeq (step a) (step b)) m) (effSeq (effSeq (step b) (step a)) m) (effSeq (step b) (effSeq (step a) m))\n");
  com_put(&t, "      (fun (i : I) => effAssoc (step a) (step b) m @ (~i))\n");
  com_put(&t, "      (fun (i : I) => effSeq (commute a b p @ i) m)\n");
  com_put(&t, "      (effAssoc (step b) (step a) m)\n");
  if (set != out->count) {
    size_t app = def_at(out, first, "traceAppend");
    com_put(&t, "def traceEval : Trace -> Eff := traceFold Eff effIsSet just (fun (a : Body) (m : Eff) => effSeq (step a) m) effSwap\n");
    com_put(&t, "def tracePropLine : (X : Type 0) -> (P : X -> Type 0) -> ((x : X) -> isProp (P x)) -> (x : X) -> (y : X) -> (p : Path X x y) -> (ex : P x) -> (ey : P y) -> PathP (fun (i : I) => P (p @ i)) ex ey :=\n");
    com_put(&t, "  fun (X : Type 0) (P : X -> Type 0) (hP : (x : X) -> isProp (P x)) (x : X) (y : X) (p : Path X x y) (ex : P x) (ey : P y) =>\n");
    com_put(&t, "    fun (i : I) => hcomp (P (p @ i)) (~i \\/ i) (fun (k : I) => [\n");
    com_put(&t, "      ~i -> hP (p @ i) (transp (fun (m : I) => P (p @ (i /\\ m))) i0 ex) ex @ k,\n");
    com_put(&t, "      i -> hP (p @ i) (transp (fun (m : I) => P (p @ (i /\\ m))) i0 ex) ey @ k ])\n");
    com_put(&t, "      (transp (fun (m : I) => P (p @ (i /\\ m))) i0 ex)\n");
    com_put(&t, "def tracePropSquare : (X : Type 0) -> (P : X -> Type 0) -> ((x : X) -> isProp (P x)) -> (x : X) -> (y : X) -> (p : Path X x y) -> (q : Path X x y) -> (s : Path (Path X x y) p q) ->\n");
    com_put(&t, "  (ihx : P x) -> (ihy : P y) -> (ihp : PathP (fun (j : I) => P (p @ j)) ihx ihy) -> (ihq : PathP (fun (j : I) => P (q @ j)) ihx ihy) ->\n");
    com_put(&t, "  PathP (fun (i : I) => PathP (fun (j : I) => P ((s @ i) @ j)) ihx ihy) ihp ihq :=\n");
    com_put(&t, "  fun (X : Type 0) (P : X -> Type 0) (hP : (x : X) -> isProp (P x)) (x : X) (y : X) (p : Path X x y) (q : Path X x y) (s : Path (Path X x y) p q)\n");
    com_put(&t, "    (ihx : P x) (ihy : P y) (ihp : PathP (fun (j : I) => P (p @ j)) ihx ihy) (ihq : PathP (fun (j : I) => P (q @ j)) ihx ihy) =>\n");
    com_put(&t, "    fun (i : I) => fun (j : I) => hcomp (P ((s @ i) @ j)) (~i \\/ i \\/ ~j \\/ j) (fun (k : I) => [\n");
    com_put(&t, "      ~i -> hP ((s @ i) @ j) (transp (fun (m : I) => P ((s @ (i /\\ m)) @ (j /\\ m))) i0 ihx) (ihp @ j) @ k,\n");
    com_put(&t, "      i -> hP ((s @ i) @ j) (transp (fun (m : I) => P ((s @ (i /\\ m)) @ (j /\\ m))) i0 ihx) (ihq @ j) @ k,\n");
    com_put(&t, "      ~j -> hP ((s @ i) @ j) (transp (fun (m : I) => P ((s @ (i /\\ m)) @ (j /\\ m))) i0 ihx) ihx @ k,\n");
    com_put(&t, "      j -> hP ((s @ i) @ j) (transp (fun (m : I) => P ((s @ (i /\\ m)) @ (j /\\ m))) i0 ihx) ihy @ k ])\n");
    com_put(&t, "      (transp (fun (m : I) => P ((s @ (i /\\ m)) @ (j /\\ m))) i0 ihx)\n");
    com_put(&t, "def traceEvalGen : (sE : isSet Eff) -> (f : Body -> Eff) -> (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) -> Trace -> Eff :=\n");
    com_put(&t, "  fun (sE : isSet Eff) (f : Body -> Eff) (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) => traceFold Eff sE just (fun (a : Body) (m : Eff) => effSeq (f a) m) fs\n");
    com_put(&t, "def evalAppendConsGen : (sE : isSet Eff) -> (f : Body -> Eff) -> (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) -> (u : Trace) -> (a : Body) -> (r : Trace) -> Path Eff (traceEvalGen sE f fs (traceAppend r u)) (effSeq (traceEvalGen sE f fs r) (traceEvalGen sE f fs u)) -> Path Eff (traceEvalGen sE f fs (traceAppend (traceCons a r) u)) (effSeq (traceEvalGen sE f fs (traceCons a r)) (traceEvalGen sE f fs u)) :=\n");
    com_put(&t, "  fun (sE : isSet Eff) (f : Body -> Eff) (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) (u : Trace) (a : Body) (r : Trace) (ih : Path Eff (traceEvalGen sE f fs (traceAppend r u)) (effSeq (traceEvalGen sE f fs r) (traceEvalGen sE f fs u))) =>\n");
    com_put(&t, "    effTrans (effSeq (f a) (traceEvalGen sE f fs (traceAppend r u))) (effSeq (f a) (effSeq (traceEvalGen sE f fs r) (traceEvalGen sE f fs u)))\n");
    com_put(&t, "      (effSeq (effSeq (f a) (traceEvalGen sE f fs r)) (traceEvalGen sE f fs u)) (effSeq (effSeq (f a) (traceEvalGen sE f fs r)) (traceEvalGen sE f fs u))\n");
    com_put(&t, "      (fun (i : I) => effSeq (f a) (ih @ i)) (fun (i : I) => effAssoc (f a) (traceEvalGen sE f fs r) (traceEvalGen sE f fs u) @ (~i)) refl\n");
    com_put(&t, "def evalAppendGen : (sE : isSet Eff) -> (f : Body -> Eff) -> (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) -> (t : Trace) -> (u : Trace) -> Path Eff (traceEvalGen sE f fs (traceAppend t u)) (effSeq (traceEvalGen sE f fs t) (traceEvalGen sE f fs u)) :=\n");
    com_put(&t, "  fun (sE : isSet Eff) (f : Body -> Eff) (fs : (a : Body) -> (b : Body) -> (m : Eff) -> Path Flag (ind a b) flagYes -> Path Eff (effSeq (f a) (effSeq (f b) m)) (effSeq (f b) (effSeq (f a) m))) (t : Trace) (u : Trace) => elim (fun (z : Trace) => Path Eff (traceEvalGen sE f fs (traceAppend z u)) (effSeq (traceEvalGen sE f fs z) (traceEvalGen sE f fs u)))\n");
    com_put(&t, "    refl\n");
    com_put(&t, "    (fun (a : Body) (r : Trace) (ih : Path Eff (traceEvalGen sE f fs (traceAppend r u)) (effSeq (traceEvalGen sE f fs r) (traceEvalGen sE f fs u))) => evalAppendConsGen sE f fs u a r ih)\n");
    com_put(&t, "    (fun (a : Body) (b : Body) (r : Trace) (ih : Path Eff (traceEvalGen sE f fs (traceAppend r u)) (effSeq (traceEvalGen sE f fs r) (traceEvalGen sE f fs u))) (h : Path Flag (ind a b) flagYes) =>\n");
    com_put(&t, "      fun (i : I) => tracePropLine Trace (fun (z : Trace) => Path Eff (traceEvalGen sE f fs (traceAppend z u)) (effSeq (traceEvalGen sE f fs z) (traceEvalGen sE f fs u))) (fun (z : Trace) => sE (traceEvalGen sE f fs (traceAppend z u)) (effSeq (traceEvalGen sE f fs z) (traceEvalGen sE f fs u)))\n");
    com_put(&t, "        (traceCons a (traceCons b r)) (traceCons b (traceCons a r)) (fun (j : I) => traceSwap a b r h j)\n");
    com_put(&t, "        (evalAppendConsGen sE f fs u a (traceCons b r) (evalAppendConsGen sE f fs u b r ih)) (evalAppendConsGen sE f fs u b (traceCons a r) (evalAppendConsGen sE f fs u a r ih)) @ i)\n");
    com_put(&t, "    (fun (x : Trace) (ihx : Path Eff (traceEvalGen sE f fs (traceAppend x u)) (effSeq (traceEvalGen sE f fs x) (traceEvalGen sE f fs u))) (y : Trace) (ihy : Path Eff (traceEvalGen sE f fs (traceAppend y u)) (effSeq (traceEvalGen sE f fs y) (traceEvalGen sE f fs u))) (p : Path Trace x y) (ihp : PathP (fun (j : I) => Path Eff (traceEvalGen sE f fs (traceAppend (p @ j) u)) (effSeq (traceEvalGen sE f fs (p @ j)) (traceEvalGen sE f fs u))) ihx ihy)\n");
    com_put(&t, "      (q : Path Trace x y) (ihq : PathP (fun (j : I) => Path Eff (traceEvalGen sE f fs (traceAppend (q @ j) u)) (effSeq (traceEvalGen sE f fs (q @ j)) (traceEvalGen sE f fs u))) ihx ihy) =>\n");
    com_put(&t, "      fun (i : I) => fun (j : I) => (tracePropSquare Trace (fun (z : Trace) => Path Eff (traceEvalGen sE f fs (traceAppend z u)) (effSeq (traceEvalGen sE f fs z) (traceEvalGen sE f fs u))) (fun (z : Trace) => sE (traceEvalGen sE f fs (traceAppend z u)) (effSeq (traceEvalGen sE f fs z) (traceEvalGen sE f fs u)))\n");
    com_put(&t, "        x y p q (fun (c : I) => fun (d : I) => traceSquash x y p q c d) ihx ihy ihp ihq @ i) @ j) t\n");
    com_put(&t, "def evalAppend : (t : Trace) -> (u : Trace) -> Path Eff (traceEval (traceAppend t u)) (effSeq (traceEval t) (traceEval u)) :=\n");
    com_put(&t, "  fun (t : Trace) (u : Trace) => evalAppendGen effIsSet step effSwap t u\n");
    com_put(&t, "def Blockchain : Type 0 := Sigma (f : Eff) (Trunc1 (fiber Trace Eff traceEval f))\n");
    com_put(&t, "def chainOf : Trace -> Blockchain := fun (t : Trace) => pack (traceEval t) (trunc1 (fiber Trace Eff traceEval (traceEval t)) (pack t refl))\n");
    com_put(&t, "def chainEval : Blockchain -> Eff := fun (c : Blockchain) => witness c\n");
    com_put(&t, "def trunc1Map2 : (A : Type 0) -> (B : Type 0) -> (C : Type 0) -> (A -> B -> C) -> Trunc1 A -> Trunc1 B -> Trunc1 C :=\n");
    com_put(&t, "  fun (A : Type 0) (B : Type 0) (C : Type 0) (h : A -> B -> C) (x : Trunc1 A) (y : Trunc1 B) =>\n");
    com_put(&t, "    fold (fun (a : A) =>\n");
    com_put(&t, "        fold (fun (b : B) => trunc1 C (h a b))\n");
    com_put(&t, "          (fun (u : Trunc1 C) (v : Trunc1 C) => fun (i : I) => squash1 C u v i)\n");
    com_put(&t, "          y)\n");
    com_put(&t, "      (fun (u : Trunc1 C) (v : Trunc1 C) => fun (i : I) => squash1 C u v i)\n");
    com_put(&t, "      x\n");
    com_put(&t, "def chainAppend : Blockchain -> Blockchain -> Blockchain :=\n");
    com_put(&t, "  fun (c : Blockchain) (d : Blockchain) =>\n");
    com_put(&t, "    pack (effSeq (witness c) (witness d))\n");
    com_put(&t, "      (trunc1Map2 (fiber Trace Eff traceEval (witness c)) (fiber Trace Eff traceEval (witness d)) (fiber Trace Eff traceEval (effSeq (witness c) (witness d)))\n");
    com_put(&t, "        (fun (p : fiber Trace Eff traceEval (witness c)) (q : fiber Trace Eff traceEval (witness d)) =>\n");
    com_put(&t, "          pack (traceAppend (witness p) (witness q))\n");
    com_put(&t, "            (effTrans (traceEval (traceAppend (witness p) (witness q))) (effSeq (traceEval (witness p)) (traceEval (witness q))) (effSeq (witness c) (traceEval (witness q))) (effSeq (witness c) (witness d))\n");
    com_put(&t, "              (evalAppend (witness p) (witness q))\n");
    com_put(&t, "              (fun (i : I) => effSeq (payload p @ i) (traceEval (witness q)))\n");
    com_put(&t, "              (fun (i : I) => effSeq (witness c) (payload q @ i))))\n");
    com_put(&t, "        (payload c) (payload d))\n");
    com_put(&t, "def chainPath : (f : Eff) -> (g : Eff) -> (p : Path Eff f g) -> (x : Trunc1 (fiber Trace Eff traceEval f)) -> (y : Trunc1 (fiber Trace Eff traceEval g)) -> Path Blockchain (pack f x) (pack g y) :=\n");
    com_put(&t, "  fun (f : Eff) (g : Eff) (p : Path Eff f g) (x : Trunc1 (fiber Trace Eff traceEval f)) (y : Trunc1 (fiber Trace Eff traceEval g)) =>\n");
    com_put(&t, "    fun (i : I) =>\n");
    com_put(&t, "      pack (p @ i)\n");
    com_put(&t, "        (squash1 (fiber Trace Eff traceEval (p @ i))\n");
    com_put(&t, "          (transp (fun (j : I) => Trunc1 (fiber Trace Eff traceEval (p @ (i /\\ j)))) (~i) x)\n");
    com_put(&t, "          (transp (fun (j : I) => Trunc1 (fiber Trace Eff traceEval (p @ (i \\/ ~j)))) i y)\n");
    com_put(&t, "          i)\n");
    /* S7 u2 (Q-S7-1 (a)): nerode s0 t u is the path in Maybe State between
       the results of t and u at the start state s0. nerodeCat composes two
       such paths. nerodeRight is L6: evalAppend at s0, then bind along r. */
    com_put(&t, "def nerode : State -> Trace -> Trace -> Type 0 := fun (s0 : State) (t : Trace) (u : Trace) => Path (Maybe State) (traceEval t s0) (traceEval u s0)\n");
    com_put(&t, "def nerodeCat : (a : Maybe State) -> (b : Maybe State) -> (c : Maybe State) -> Path (Maybe State) a b -> Path (Maybe State) b c -> Path (Maybe State) a c :=\n");
    com_put(&t, "  fun (a : Maybe State) (b : Maybe State) (c : Maybe State) (p : Path (Maybe State) a b) (q : Path (Maybe State) b c) =>\n");
    com_put(&t, "    fun (i : I) => hcomp (Maybe State) (~i \\/ i) (fun (k : I) => [ ~i -> a, i -> q @ k ]) (p @ i)\n");
    com_put(&t, "def nerodeRefl : (s0 : State) -> (t : Trace) -> nerode s0 t t := fun (s0 : State) (t : Trace) => refl\n");
    com_put(&t, "def nerodeSym : (s0 : State) -> (t : Trace) -> (u : Trace) -> nerode s0 t u -> nerode s0 u t := fun (s0 : State) (t : Trace) (u : Trace) (r : nerode s0 t u) => fun (i : I) => r @ (~i)\n");
    com_put(&t, "def nerodeTrans : (s0 : State) -> (t : Trace) -> (u : Trace) -> (v : Trace) -> nerode s0 t u -> nerode s0 u v -> nerode s0 t v :=\n");
    com_put(&t, "  fun (s0 : State) (t : Trace) (u : Trace) (v : Trace) (p : nerode s0 t u) (q : nerode s0 u v) => nerodeCat (traceEval t s0) (traceEval u s0) (traceEval v s0) p q\n");
    com_put(&t, "def nerodeRight : (s0 : State) -> (t : Trace) -> (u : Trace) -> (k : Trace) -> nerode s0 t u -> nerode s0 (traceAppend t k) (traceAppend u k) :=\n");
    com_put(&t, "  fun (s0 : State) (t : Trace) (u : Trace) (k : Trace) (r : nerode s0 t u) =>\n");
    com_put(&t, "    nerodeCat (traceEval (traceAppend t k) s0) (effSeq (traceEval t) (traceEval k) s0) (traceEval (traceAppend u k) s0)\n");
    com_put(&t, "      (fun (i : I) => (evalAppend t k @ i) s0)\n");
    com_put(&t, "      (nerodeCat (effSeq (traceEval t) (traceEval k) s0) (effSeq (traceEval u) (traceEval k) s0) (traceEval (traceAppend u k) s0)\n");
    com_put(&t, "        (fun (i : I) => bind (r @ i) (fun (x : State) => traceEval k x))\n");
    com_put(&t, "        (fun (i : I) => (evalAppend u k @ (~i)) s0))\n");
    /* S7 u3a (Q-S7-2 (a)): Ledger s0 is the set quotient of Trace by
       nerode s0. ledgerIn is a point, ledgerGlue is a path at a Nerode
       pair and ledgerSquash makes Ledger s0 a set. ledgerFold maps
       Ledger s0 into a set M from a map of traces that respects nerode s0. */
    com_put(&t, "family Ledger (s0 : State) := ledgerIn (ledgerOf : Trace)\n");
    com_put(&t, "  | ledgerGlue (ledgerA : Trace) (ledgerB : Trace) (ledgerR : nerode s0 ledgerA ledgerB) (ledgerI : I)\n");
    com_put(&t, "    [ ~ledgerI -> ledgerIn s0 ledgerA, ledgerI -> ledgerIn s0 ledgerB ]\n");
    com_put(&t, "  | ledgerSquash (ledgerFrom : Ledger s0) (ledgerTo : Ledger s0) (ledgerLeft : Path (Ledger s0) ledgerFrom ledgerTo) (ledgerRight : Path (Ledger s0) ledgerFrom ledgerTo) (ledgerSqI : I) (ledgerSqJ : I)\n");
    com_put(&t, "    [ ~ledgerSqI -> ledgerLeft @ ledgerSqJ, ledgerSqI -> ledgerRight @ ledgerSqJ, ~ledgerSqJ -> ledgerFrom, ledgerSqJ -> ledgerTo ]\n");
    com_put(&t, "def ledgerIsSet : (s0 : State) -> isSet (Ledger s0) :=\n");
    com_put(&t, "  fun (s0 : State) (x : Ledger s0) (y : Ledger s0) (p : Path (Ledger s0) x y) (q : Path (Ledger s0) x y) => fun (i : I) => fun (j : I) => ledgerSquash s0 x y p q i j\n");
    com_put(&t, "def ledgerFold : (s0 : State) -> (M : Type 0) -> isSet M -> (f : Trace -> M) -> ((t : Trace) -> (u : Trace) -> nerode s0 t u -> Path M (f t) (f u)) -> Ledger s0 -> M :=\n");
    com_put(&t, "  fun (s0 : State) (M : Type 0) (sM : isSet M) (f : Trace -> M) (g : (t : Trace) -> (u : Trace) -> nerode s0 t u -> Path M (f t) (f u)) (l : Ledger s0) =>\n");
    com_put(&t, "    fold (fun (t : Trace) => f t)\n");
    com_put(&t, "      (fun (t : Trace) (u : Trace) (r : nerode s0 t u) => fun (i : I) => g t u r @ i)\n");
    com_put(&t, "      (fun (x : M) (y : M) (p : Path M x y) (q : Path M x y) => fun (i : I) => fun (j : I) => (sM x y p q @ i) @ j) l\n");
    /* S7 u3b (Q-S7-5 (a), Q-S7-9 (a)): apply adds the body b at the end of
       each trace. A Nerode pair stays a Nerode pair (nerodeRight), thus the
       glue case is a ledgerGlue path. ledgerEval runs a Ledger value at s0
       and query reads one value of the result state. The point case of
       ledgerEval is refl, but that lemma is not in the prelude: at an open
       trace its check can reach the arena limit (examples/step-hygiene.lang). */
    com_put(&t, "def apply : (s0 : State) -> Ledger s0 -> Body -> Ledger s0 :=\n");
    com_put(&t, "  fun (s0 : State) (l : Ledger s0) (b : Body) => ledgerFold s0 (Ledger s0) (ledgerIsSet s0)\n");
    com_put(&t, "    (fun (t : Trace) => ledgerIn s0 (traceAppend t (traceOne b)))\n");
    com_put(&t, "    (fun (t : Trace) (u : Trace) (r : nerode s0 t u) => fun (i : I) => ledgerGlue s0 (traceAppend t (traceOne b)) (traceAppend u (traceOne b)) (nerodeRight s0 t u (traceOne b) r) i) l\n");
    com_put(&t, "def ledgerEval : (s0 : State) -> Ledger s0 -> Maybe State :=\n");
    com_put(&t, "  fun (s0 : State) (l : Ledger s0) => ledgerFold s0 (Maybe State) (maybeIsSet State (piIsSet Key Val valIsSet))\n");
    com_put(&t, "    (fun (t : Trace) => traceEval t s0)\n");
    com_put(&t, "    (fun (t : Trace) (u : Trace) (r : nerode s0 t u) => fun (i : I) => r @ i) l\n");
    com_put(&t, "def query : (s0 : State) -> (A : Type 0) -> isSet A -> (State -> A) -> Ledger s0 -> Maybe A :=\n");
    com_put(&t, "  fun (s0 : State) (A : Type 0) (sA : isSet A) (obs : State -> A) (l : Ledger s0) => bind (ledgerEval s0 l) (fun (x : State) => some (obs x))\n");
    /* S7 u4 (Q-S7-4 (a), Q-S7-6 (a), Q-S7-10 (a)): traceAppendEps is the
       right unit law of traceAppend, an elim in the evalAppendGen form (the
       motive is a path of Trace, thus a prop by traceIsSet). prefix t u is
       the truncated type of a k with traceAppend t k = u (the sugar
       `t <= u`). Compatible t u has a common upper bound w of t and u. */
    com_put(&t, "def appendEpsCons : (a : Body) -> (r : Trace) -> Path Trace (traceAppend r traceEps) r -> Path Trace (traceAppend (traceCons a r) traceEps) (traceCons a r) :=\n");
    com_put(&t, "  fun (a : Body) (r : Trace) (ih : Path Trace (traceAppend r traceEps) r) => fun (i : I) => traceCons a (ih @ i)\n");
    com_put(&t, "def traceAppendEps : (t : Trace) -> Path Trace (traceAppend t traceEps) t :=\n");
    com_put(&t, "  fun (t : Trace) => elim (fun (z : Trace) => Path Trace (traceAppend z traceEps) z)\n");
    com_put(&t, "    refl\n");
    com_put(&t, "    (fun (a : Body) (r : Trace) (ih : Path Trace (traceAppend r traceEps) r) => appendEpsCons a r ih)\n");
    com_put(&t, "    (fun (a : Body) (b : Body) (r : Trace) (ih : Path Trace (traceAppend r traceEps) r) (h : Path Flag (ind a b) flagYes) =>\n");
    com_put(&t, "      fun (i : I) => tracePropLine Trace (fun (z : Trace) => Path Trace (traceAppend z traceEps) z) (fun (z : Trace) => traceIsSet (traceAppend z traceEps) z)\n");
    com_put(&t, "        (traceCons a (traceCons b r)) (traceCons b (traceCons a r)) (fun (j : I) => traceSwap a b r h j)\n");
    com_put(&t, "        (appendEpsCons a (traceCons b r) (appendEpsCons b r ih)) (appendEpsCons b (traceCons a r) (appendEpsCons a r ih)) @ i)\n");
    com_put(&t, "    (fun (x : Trace) (ihx : Path Trace (traceAppend x traceEps) x) (y : Trace) (ihy : Path Trace (traceAppend y traceEps) y) (p : Path Trace x y) (ihp : PathP (fun (j : I) => Path Trace (traceAppend (p @ j) traceEps) (p @ j)) ihx ihy)\n");
    com_put(&t, "      (q : Path Trace x y) (ihq : PathP (fun (j : I) => Path Trace (traceAppend (q @ j) traceEps) (q @ j)) ihx ihy) =>\n");
    com_put(&t, "      fun (i : I) => fun (j : I) => (tracePropSquare Trace (fun (z : Trace) => Path Trace (traceAppend z traceEps) z) (fun (z : Trace) => traceIsSet (traceAppend z traceEps) z)\n");
    com_put(&t, "        x y p q (fun (c : I) => fun (d : I) => traceSquash x y p q c d) ihx ihy ihp ihq @ i) @ j) t\n");
    com_put(&t, "def prefix : Trace -> Trace -> Type 0 :=\n");
    com_put(&t, "  fun (t : Trace) (u : Trace) => Trunc1 (Sigma (k : Trace) (Path Trace (traceAppend t k) u))\n");
    com_put(&t, "def Compatible : Trace -> Trace -> Type 0 :=\n");
    com_put(&t, "  fun (t : Trace) (u : Trace) => Trunc1 (Sigma (w : Trace) (Prod (prefix t w) (prefix u w)))\n");
    com_put(&t, "def prefixRefl : (t : Trace) -> prefix t t :=\n");
    com_put(&t, "  fun (t : Trace) => trunc1 (Sigma (k : Trace) (Path Trace (traceAppend t k) t)) (pack traceEps (traceAppendEps t))\n");
    com_put(&t, "def prefixAppend : (t : Trace) -> (k : Trace) -> prefix t (traceAppend t k) :=\n");
    com_put(&t, "  fun (t : Trace) (k : Trace) => trunc1 (Sigma (m : Trace) (Path Trace (traceAppend t m) (traceAppend t k))) (pack k refl)\n");
    com_put(&t, "def compatibleOfPrefix : (t : Trace) -> (u : Trace) -> prefix t u -> Compatible t u :=\n");
    com_put(&t, "  fun (t : Trace) (u : Trace) (p : prefix t u) => trunc1 (Sigma (w : Trace) (Prod (prefix t w) (prefix u w))) (pack u (pair p (prefixRefl u)))\n");
    last = set > last ? set : last;
    last = app != out->count && app > last ? app : last;
  }
  if (!t.ok)
    return diag_fail(diag, "OOM", NULL, "the generated text of commute is too long");
  if (!lex_internal(arena, COMMUTE_SOURCE_NAME, t.s, t.len, &toks, diag)
      || !parse_source(arena, COMMUTE_SOURCE_NAME, ORIGIN_DOMAIN, &toks, &kernel, diag))
    return 0;
  for (i = 0; i < kernel.count; i++) {
    kernel.items[i].name = com_name(arena, kernel.items[i].name, &ok);
    kernel.items[i].type = com_term(arena, kernel.items[i].type, &ok);
    kernel.items[i].body = com_term(arena, kernel.items[i].body, &ok);
  }
  items = ok ? arena_alloc(arena, (out->count + kernel.count) * sizeof *items) : NULL;
  if (items == NULL)
    return 0;
  memcpy(items, out->items, (last + 1u) * sizeof *items);
  memcpy(items + last + 1u, kernel.items, kernel.count * sizeof *items);
  memcpy(items + last + 1u + kernel.count, out->items + last + 1u, (out->count - last - 1u) * sizeof *items);
  out->items = items;
  out->count += kernel.count;
  out->cap = out->count;
  return 1;
}

/* The matrix row of the footprint families A and B, or NULL. The rows have
   a <= b only and ind is symmetric, so the row (B, A) also gives (A, B);
   then *SWAP is 1 (when A and B differ). A row is found by its names, not
   by its index. */
const IndRow *front_ind_row(const IndMatrix *ind, const char *a, const char *b, int *swap) {
  uint32_t r;
  *swap = 0;
  for (r = 0; r < ind->row_count; r++) {
    const IndRow *row = &ind->rows[r];
    int ab = strcmp(row->a, a) == 0 && strcmp(row->b, b) == 0;
    int ba = strcmp(row->a, b) == 0 && strcmp(row->b, a) == 0;
    if (ab || ba) {
      *swap = !ab;
      return row;
    }
  }
  return NULL;
}

/* 1 when the matrix row of the footprint families A and B is IND_ALWAYS. */
static int ind_always(const IndMatrix *ind, const char *a, const char *b) {
  int swap = 0;
  const IndRow *row = front_ind_row(ind, a, b, &swap);
  return row != NULL && row->verdict == IND_ALWAYS;
}

/* The case of ind at x : F (ind#x) and y : G (ind#y) (quotient-lang S6
   u4c2, USER rulings Q-S6-20 (a) and Q-S6-21 (a)). An IND_ALWAYS row gives
   flagYes. An IND_IF row with the slot def commute<F><G> gives the AND,
   nested to the right, of `flagIf (keyEq KF KG) flagNo flagYes` over all
   the clauses of the row, in their order: KF is the key of x and KG the
   key of y. At a row stored as (G, F), the pattern ka is the key of y and
   kb the key of x. The other rows give flagNo. */
static const Term *ind_leaf(StepBuild *b, const DeclList *decls, const IndMatrix *ind, const char *f, const char *g) {
  int swap = 0;
  const IndRow *row = front_ind_row(ind, f, g, &swap);
  const char *slot;
  const Term *acc = NULL;
  uint32_t k;
  if (ind_always(ind, f, g))
    return step_var(b, "flagYes");
  if (row == NULL || row->verdict != IND_IF || row->clause_count == 0u)
    return step_var(b, "flagNo");
  slot = com_slot(b->arena, f, g);
  if (slot == NULL) {
    b->ok = 0;
    return NULL;
  }
  if (program_def_at(decls, 0u, slot) == decls->count)
    return step_var(b, "flagNo");
  for (k = 0; k < row->clause_count; k++) {
    if (row->clauses[k].ka == NULL || row->clauses[k].kb == NULL)
      return step_var(b, "flagNo");
  }
  for (k = row->clause_count; k > 0u; k--) {
    const IndClause *cl = &row->clauses[k - 1u];
    const Term *kf = step_key_on(b, swap ? cl->kb : cl->ka, "ind#x");
    const Term *kg = step_key_on(b, swap ? cl->ka : cl->kb, "ind#y");
    const Term *ne = step_app(b, step_app(b, step_app(b, step_var(b, "flagIf"), step_app(b, step_app(b, step_var(b, "keyEq"), kf), kg)), step_var(b, "flagNo")), step_var(b, "flagYes"));
    acc = acc == NULL ? ne : step_app(b, step_app(b, step_app(b, step_var(b, "flagIf"), ne), acc), step_var(b, "flagNo"));
  }
  return acc;
}

const Term *front_ind_body(Arena *arena, const DeclList *decls, const IndMatrix *ind, int line, int col) {
  StepBuild b = {arena, 0, 0, 1};
  const Term *e;
  size_t i;
  size_t j;
  b.line = line;
  b.col = col;
  e = step_app(&b, step_var(&b, "elim"), step_lam(&b, "ind#u", step_var(&b, "Body"), step_var(&b, "Flag")));
  for (i = 0; i < decls->count; i++) {
    const Decl *fi = &decls->items[i];
    const Term *v;
    if (!footprint_family(fi))
      continue;
    v = step_app(&b, step_var(&b, "elim"), step_lam(&b, "ind#v", step_var(&b, "Body"), step_var(&b, "Flag")));
    for (j = 0; j < decls->count; j++) {
      const Decl *fj = &decls->items[j];
      if (!footprint_family(fj))
        continue;
      v = step_app(&b, v, step_lam(&b, "ind#y", step_var(&b, fj->name), ind_leaf(&b, decls, ind, fi->name, fj->name)));
    }
    v = step_app(&b, v, step_var(&b, "ind#b"));
    e = step_app(&b, e, step_lam(&b, "ind#x", step_var(&b, fi->name), v));
  }
  e = step_app(&b, e, step_var(&b, "ind#a"));
  e = step_lam(&b, "ind#a", step_var(&b, "Body"), step_lam(&b, "ind#b", step_var(&b, "Body"), e));
  return b.ok ? e : NULL;
}

const Term *front_slot_h_type(Arena *arena, const Term *type) {
  StepBuild b = {arena, 0, 0, 1};
  const Term *g = type != NULL && type->kind == TERM_PI ? type->right : NULL;
  const char *bf;
  const char *bg;
  const Term *h;
  Term *outer;
  Term *inner;
  if (g == NULL || g->kind != TERM_PI || type->name == NULL || g->name == NULL || type->left == NULL || type->left->kind != TERM_VAR || g->left == NULL || g->left->kind != TERM_VAR)
    return type;
  bf = front_prefixed(arena, "body", type->left->name);
  bg = front_prefixed(arena, "body", g->left->name);
  if (bf == NULL || bg == NULL)
    return NULL;
  b.line = type->line;
  b.col = type->col;
  h = step_app(&b, step_app(&b, step_var(&b, "ind"), step_app(&b, step_var(&b, bf), step_var(&b, type->name))), step_app(&b, step_var(&b, bg), step_var(&b, g->name)));
  h = step_app(&b, step_app(&b, step_app(&b, step_var(&b, "Path"), step_var(&b, "Flag")), h), step_var(&b, "flagYes"));
  outer = b.ok ? arena_alloc(arena, sizeof *outer) : NULL;
  inner = outer != NULL ? arena_alloc(arena, sizeof *inner) : NULL;
  if (inner == NULL)
    return NULL;
  *outer = *type;
  *inner = *g;
  inner->right = step_node(&b, TERM_PI, "com#h", 0u, h, g->right);
  outer->right = inner;
  return b.ok ? outer : NULL;
}

const Term *front_leaf_h_body(Arena *arena, const Term *body) {
  StepBuild b = {arena, 0, 0, 1};
  const Term *l2 = body != NULL && body->kind == TERM_LAM ? body->right : NULL;
  const Term *l3 = l2 != NULL && l2->kind == TERM_LAM ? l2->right : NULL;
  const Term *fx = l3 != NULL && l3->kind == TERM_LAM ? l3->right : NULL;
  Term *c1;
  Term *c2;
  Term *c3;
  Term *c4;
  if (fx == NULL || fx->kind != TERM_APP || l3->name == NULL || fx->left == NULL || fx->left->kind != TERM_VAR || fx->left->name == NULL || strcmp(fx->left->name, "funExt") != 0)
    return body;
  b.line = fx->line;
  b.col = fx->col;
  c1 = arena_alloc(arena, sizeof *c1);
  c2 = c1 != NULL ? arena_alloc(arena, sizeof *c2) : NULL;
  c3 = c2 != NULL ? arena_alloc(arena, sizeof *c3) : NULL;
  c4 = c3 != NULL ? arena_alloc(arena, sizeof *c4) : NULL;
  if (c4 == NULL)
    return NULL;
  *c1 = *body;
  *c2 = *l2;
  *c3 = *l3;
  *c4 = *fx;
  c4->right = step_app(&b, fx->right, step_var(&b, l3->name));
  c3->right = c4;
  c2->right = c3;
  c1->right = c2;
  return b.ok ? c1 : NULL;
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
      && set_after_step(arena, first, out, diag)
      && step_defs(arena, first, out)
      && body_family(arena, first, out)
      && body_eq_after_body(arena, first, out, diag)
      && body_step(arena, first, out)
      && ind_placeholder(arena, first, out)
      && trace_after_ind(arena, first, out, diag)
      && foata_after_trace(arena, first, out, diag)
      && foata_eq_after_foata(arena, first, out, diag)
      && body_commute(arena, first, out, diag)
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
      && set_after_step(arena, first, out, diag)
      && step_defs(arena, first, out)
      && body_family(arena, first, out)
      && body_eq_after_body(arena, first, out, diag)
      && body_step(arena, first, out)
      && ind_placeholder(arena, first, out)
      && trace_after_ind(arena, first, out, diag)
      && foata_after_trace(arena, first, out, diag)
      && foata_eq_after_foata(arena, first, out, diag)
      && body_commute(arena, first, out, diag)
      && auth_after_witness(arena, first, out, diag)
      && agg_after_sig(arena, first, out, diag)
      && qc_after_signs(arena, first, out, diag);
}
