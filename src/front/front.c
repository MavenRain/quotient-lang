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
   directly after the program def Key. A footprint is a finite subset of
   keys. The Key slot must be first-order data (check.c, check_sig). */
#define KEY_SOURCE_NAME "kernel/key.lang"

static const char key_source[] =
  "def Footprint : Type 0 := Pfin Key\n";

static const char *const KEY_AFTER[] = {"Key"};

/* The key prelude goes directly after the program def Key. */
static int key_after_key(Arena *arena, size_t first, DeclList *out, Diag *diag) {
  return splice_after(arena, first, KEY_AFTER, 1u, KEY_SOURCE_NAME, key_source, sizeof key_source - 1u, out, diag);
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
      && value_after_asset(arena, first, out, diag)
      && key_after_key(arena, first, out, diag);
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
      && value_after_asset(arena, first, out, diag)
      && key_after_key(arena, first, out, diag);
}
