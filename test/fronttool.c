/* Domain declaration regressions use the same parser and checker as langc. */
#include <stdio.h>
#include <string.h>

#include "front/check.h"
#include "front/lexer.h"
#include "front/parser.h"

/* checked parses TEXT with ORIGIN and checks it in MODE. A domain row is
   trusted text in kit mode; a guest row (orbit-lang S3) is program text in
   guest mode. */
static int checked_in(const char *domain_text, const char *text, Origin origin, CheckMode mode, const char *want) {
  Arena arena;
  Diag diag;
  TokenList tokens = {0};
  DeclList decls = {0};
  Machine machine;
  arena_init(&arena, (size_t)1 << 24);
  diag_init(&diag);
  int ok = domain_text == NULL
    || (lex_source(&arena, "test-prelude", domain_text, strlen(domain_text), &tokens, &diag)
        && parse_source(&arena, "test-prelude", ORIGIN_DOMAIN, &tokens, &decls, &diag));
  ok = ok && lex_source(&arena, "test-domain", text, strlen(text), &tokens, &diag)
    && parse_source(&arena, "test-domain", origin, &tokens, &decls, &diag)
    && check_program(&arena, &decls, &machine, &diag, mode);
  int passed = want == NULL ? ok : !ok && diag.code != NULL && strcmp(diag.code, want) == 0;
  if (passed && want == NULL && machine.has_state) {
    const CtorInfo *ci = &machine.ctors[machine.families[machine.state_family].first_ctor];
    for (uint32_t i = 0; i < ci->field_count; i++)
      passed &= eval_core(&machine, NULL, ci->fields[i].type) != NULL;
  }
  if (!passed) {
    fprintf(stderr, "FAIL %s: wanted %s, got %s: %s\n", mode == CHECK_KIT ? "domain" : "guest",
            want == NULL ? "ok" : want, ok ? "ok" : diag.code == NULL ? "no diagnostic" : diag.code, text);
  }
  arena_release(&arena);
  return passed;
}

static int checked(const char *text, Origin origin, CheckMode mode, const char *want) {
  return checked_in(NULL, text, origin, mode, want);
}

static int law_guest(const char *text, const char *want) {
  return checked_in(
    "family Size := sz0 | szS (szPred : Size)\n"
    "family Trunc1 (A : Type 0) := trunc1 (trunc1Of : A)\n"
    "  | squash1 (squash1X : Trunc1 A) (squash1Y : Trunc1 A) (i : I) [ ~i -> squash1X, i -> squash1Y ]\n"
    "sealed family Sl (A : Type 0) := slEta (slOf : A)\n"
    "law def slOut : (A : Type 0) -> Sl A -> A := fun A c => fold (fun a => a) c\n",
    text, ORIGIN_PROGRAM, CHECK_GUEST, want);
}

static int domain(const char *text, const char *want) {
  return checked(text, ORIGIN_DOMAIN, CHECK_KIT, want);
}

static int guest(const char *text, const char *want) {
  return checked(text, ORIGIN_PROGRAM, CHECK_GUEST, want);
}

static int normal_roundtrip_in(const char *domain_text, const char *type, const char *body) {
  char source[4096];
  char normal[2048];
  Arena arena;
  Diag diag;
  TokenList tokens = {0};
  DeclList decls = {0};
  Machine machine;
  snprintf(source, sizeof source, "%s\ndef value : %s := %s", domain_text, type, body);
  arena_init(&arena, (size_t)1 << 24);
  diag_init(&diag);
  int ok = lex_source(&arena, "test-roundtrip", source, strlen(source), &tokens, &diag)
    && parse_source(&arena, "test-roundtrip", ORIGIN_DOMAIN, &tokens, &decls, &diag)
    && check_program(&arena, &decls, &machine, &diag, CHECK_KIT);
  if (ok)
    ok = value_print(&machine, NULL, 0, def_value(&machine, 0), normal, sizeof normal);
  if (!ok) {
    fputs("FAIL normal roundtrip: ", stderr);
    diag_print(&diag, stderr);
  }
  arena_release(&arena);
  if (!ok)
    return 0;
  snprintf(source, sizeof source, "%s\ndef value : %s := %s", domain_text, type, normal);
  return domain(source, NULL);
}

static int normal_roundtrip(const char *type, const char *body) {
  return normal_roundtrip_in("", type, body);
}

static int len_roundtrip(const char *type, const char *body) {
  return normal_roundtrip_in(
    "family FreeMon (A : Type 0) := fmEta (fmEtaOf : A) | fmUnit\n"
    "  | fmSquash (fmFrom : FreeMon A) (fmTo : FreeMon A)"
    " (fmPathL : Path (FreeMon A) fmFrom fmTo) (fmPathR : Path (FreeMon A) fmFrom fmTo) (i : I) (j : I)\n"
    "    [ ~i -> fmPathL @ j, i -> fmPathR @ j, ~j -> fmFrom, j -> fmTo ]\n",
    type, body);
}

static int internal_print_refused(const char *type, const char *body) {
  char source[512];
  Arena arena;
  Diag diag;
  TokenList tokens = {0};
  DeclList decls = {0};
  Machine machine;
  FILE *out = tmpfile();
  FILE *err = tmpfile();
  int ok;
  snprintf(source, sizeof source,
    "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)\n"
    "def value : %s := %s\n", type, body);
  if (out == NULL || err == NULL) {
    if (out != NULL) fclose(out);
    if (err != NULL) fclose(err);
    return 0;
  }
  arena_init(&arena, (size_t)1 << 24);
  diag_init(&diag);
  ok = lex_source(&arena, "test-internal-print", source, strlen(source), &tokens, &diag)
    && parse_source(&arena, "test-internal-print", ORIGIN_DOMAIN, &tokens, &decls, &diag)
    && check_program(&arena, &decls, &machine, &diag, CHECK_KIT);
  ok = ok && eval_command(&machine, "value", NULL, 0, out, err) == 1
    && diag.code != NULL && strcmp(diag.code, "EVAL_PRINT") == 0
    && ftell(out) == 0;
  if (!ok) fputs("FAIL generated cofamily names must not print as source\n", stderr);
  fclose(out);
  fclose(err);
  arena_release(&arena);
  return ok;
}

int main(void) {
  int ok = 1;
  /* Diagnostics can print binders while constructor slots are still unnamed. */
  ok &= domain("state State := makeState (value : fun (x : Nat) => x)", "TYPE_MISMATCH");
  /* Time words are forbidden in local scopes as well as declarations. */
  ok &= domain("def bad : (now : Nat) -> Nat := fun x => x", "REFUSE_TIME");
  ok &= domain("def bad : Nat -> Nat := fun clock => clock", "REFUSE_TIME");
  ok &= domain("def bad : Nat -> Nat := fun time => 0", "REFUSE_TIME");
  ok &= domain("def bad : Path Nat 0 0 := fun (block : I) => 0", "REFUSE_TIME");
  ok &= domain("family Test (timestamp : Type 0) := makeTest (payload : timestamp)", "REFUSE_TIME");
  ok &= domain("def bad : Path Nat 0 0 := fun epoch => 0", "REFUSE_TIME");
  /* Counting an open higher cell must preserve its path boundaries. */
  ok &= len_roundtrip(
    "(r : FreeMon Unit) -> (p : Path (FreeMon Unit) (fmUnit Unit) r) -> Path Nat 0 (len Unit r)",
    "fun r p => fun (j : I) => len Unit (hcomp (FreeMon Unit) j (fun (i : I) => [ j -> p @ i ]) (fmUnit Unit))");
  ok &= len_roundtrip(
    "(r : FreeMon Unit) -> (p : Path (FreeMon Unit) (fmUnit Unit) r) -> Path Nat 0 (len Unit r)",
    "fun r p => fun j => len Unit (fmSquash Unit (fmUnit Unit) r p p j j)");
  ok &= len_roundtrip(
    "(p : Path (FreeMon Unit) (fmUnit Unit) (fmUnit Unit)) -> "
    "PathP (fun (j : I) => Path Nat (len Unit (p @ j)) (len Unit (p @ j))) refl refl",
    "fun p => fun j => fun i => len Unit (fmSquash Unit (fmUnit Unit) (fmUnit Unit) p p i j)");
  ok &= len_roundtrip(
    "Path Nat (len Unit (hcomp (FreeMon Unit) i0 (fun (i : I) => [ ]) (fmUnit Unit))) 0", "refl");
  ok &= internal_print_refused("Type 0", "Strm Unit");
  ok &= internal_print_refused("Strm Unit", "strmCorec Unit Unit (fun s => s) (fun s => s) unit");
  ok &= normal_roundtrip("Map Nat Nat -> Nat", "fun m => mapGet m 0");
  ok &= normal_roundtrip("Map Nat Nat -> Map Nat Nat", "fun m => mapSet m 0 1");
  /* Recursive occurrences under function domains remain forbidden in paths. */
  ok &= domain("family Bad := base | mkBad (x : Bad) "
               "(p : Path (Bad -> Bad) (fun (y : Bad) => x) (fun (y : Bad) => x))",
               "DOMAIN_FAMILY");
  /* The empty domain (sealed-lang S2, R21) lexes, parses and checks. */
  ok &= domain("", NULL);
  /* Elimination consumes its scrutinee before applying a functional result. */
  ok &= guest("def applyUnit : Unit -> Unit -> Unit := fun (u : Unit) (v : Unit) => "
              "elim (fun (w : Unit) => Unit -> Unit) (fun x => x) u v", NULL);
  ok &= guest("def applySum : Sum Unit Unit -> Unit -> Unit := fun (s : Sum Unit Unit) (v : Unit) => "
              "elim (fun (t : Sum Unit Unit) => Unit -> Unit) (fun a x => x) (fun b x => x) s v", NULL);
  ok &= guest("def choose : Sum Unit Unit -> Unit := "
              "elim (fun (s : Sum Unit Unit) => Unit) (fun u => u) (fun u => u)", NULL);
  ok &= normal_roundtrip("Unit -> Unit", "fun (u : Unit) => elim (fun (v : Unit) => Unit) unit u");
  ok &= normal_roundtrip("Sum Unit Unit -> Unit", "fun (s : Sum Unit Unit) => "
                         "elim (fun (t : Sum Unit Unit) => Unit) (fun u => u) (fun u => u) s");
  ok &= normal_roundtrip("(A : Type 0) -> (s : Sum A Unit) -> Path (Sum A Unit) s s", "fun (A : Type 0) (s : Sum A Unit) => "
                         "elim (fun (t : Sum A Unit) => Path (Sum A Unit) t t) (fun a => refl) (fun u => refl) s");
  ok &= guest("def s : Sum Unit Unit := inl unit\n"
              "def left : (v : Unit) -> Path Unit (elim (fun (t : Sum Unit Unit) => Unit -> Unit) "
              "(fun a x => x) (fun b x => unit) s v) v := fun v => refl\n"
              "def t : Sum Unit Unit := inr unit\n"
              "def right : (v : Unit) -> Path Unit (elim (fun (t : Sum Unit Unit) => Unit -> Unit) "
              "(fun a x => x) (fun b x => unit) t v) unit := fun v => refl\n"
              "def one : (v : Unit) -> Path Unit (elim (fun (u : Unit) => Unit -> Unit) "
              "(fun x => x) unit v) v := fun v => refl", NULL);
  ok &= guest("def bad : Unit -> Unit := fun (u : Unit) => elim (fun v => unit) unit u", "TYPE_MISMATCH");
  ok &= guest("def bad : Unit -> Unit := fun (u : Unit) => "
              "elim (fun (t : Sum Unit Unit) => Unit) (fun a => a) (fun b => b) u", "TYPE_MISMATCH");
  ok &= guest("def bad : Unit -> Unit := fun (u : Unit) => "
              "elim (fun (v : Unit) => Unit) unit (inl u)", "TYPE_INFER");
  /* Family eliminators can await their scrutinee. The arity comes from
     the final motive domain, including for named and indexed motives. */
  ok &= domain("family N := zero | succ (pred : N)\n"
               "def id : N -> N := elim (fun (n : N) => N) zero (fun n ih => succ ih)", NULL);
  ok &= domain("family N := zero | succ (pred : N)\n"
               "def P : N -> Type 0 := fun n => N\n"
               "def id : N -> N := elim P zero (fun n ih => succ ih)", NULL);
  ok &= normal_roundtrip_in("family N := zero | succ (pred : N)", "N -> N",
                            "elim (fun n => N) zero (fun n ih => succ ih)");
  ok &= domain("family N := zero | succ (pred : N)\n"
               "family V : N -> Type 0 := nilV : V zero | consV (vlen : N) (tailV : V vlen) : V (succ vlen)\n"
               "def id : (n : N) -> V n -> N := fun n => "
               "elim (fun (k : N) (v : V k) => N) zero (fun k t ih => succ ih)", NULL);
  ok &= domain("family N := zero | succ (pred : N)\n"
               "family V : N -> Type 0 := nilV : V zero | consV (vlen : N) (tailV : V vlen) : V (succ vlen) | altV (altLen : N) : V altLen\n"
               "def id : (n : N) -> V n -> N := fun n => "
               "elim (fun (k : N) (v : V k) => N) zero (fun k t ih => succ ih) (fun k => k)", NULL);
  /* A saturated eliminator with a functional result still consumes the
     scrutinee before the result arguments. */
  ok &= domain("family N := zero | succ (pred : N)\n"
               "def id : N -> N -> N := fun n => elim (fun (k : N) => N -> N) (fun x => x) (fun k ih x => succ (ih x)) n\n"
               "def reduction : Path N (id (succ zero) zero) (succ zero) := refl", NULL);
  /* Bare indexed motives accept and check annotations on later binders. */
  ok &= domain("family N := zero | succ (pred : N)\n"
               "family V : N -> Type 0 := nilV : V zero | consV (vlen : N) (tailV : V vlen) : V (succ vlen)\n"
               "def id : (n : N) -> V n -> N := fun n v => "
               "elim (fun k => fun (t : V k) => N) zero (fun k t ih => succ ih) v", NULL);
  ok &= domain("family N := zero | succ (pred : N)\n"
               "family V : N -> Type 0 := nilV : V zero | consV (vlen : N) (tailV : V vlen) : V (succ vlen)\n"
               "def bad : (n : N) -> V n -> N := fun n v => "
               "elim (fun k => fun (t : N) => N) zero (fun k t ih => succ ih) v", "TYPE_MISMATCH");
  ok &= domain("family F := makeF [ i1 -> missing ]", "DOMAIN_FAMILY");
  ok &= domain("family F := makeF [ ]", "DOMAIN_FAMILY");
  /* A path constructor's fields are not record projections: projection
     would discard its boundary at a neutral interval. */
  ok &= domain("family Only := arc (arcFrom : Only) (arcTo : Only) (i : I) "
               "[ ~i -> arcFrom, i -> arcTo ]\n"
               "def bad : (x : Only) -> (y : Only) -> Path Only (arcFrom x) (arcFrom y) := "
               "fun x y => fun (i : I) => arcFrom (arc x y i)", "NAME_UNKNOWN");
  ok &= domain("family T := pt (value : Nat) | arc (previous : T) (i : I) "
               "[ ~i -> pt (fold (fun n => n) 1 previous), i -> pt (fold (fun n => n) 1 previous) ]", "HIT_BOUNDARY");
  /* Indexed families and blocks (S6). hiit-wrong-index: an end of a path
     constructor is the family at another index. hiit-no-result: a
     constructor of an indexed family states no result. block-order: a
     header names a later sort of its block. index-prop: Prop is not a type
     in an index telescope (rule R4). block-ok: a field names a later sort. */
  ok &= domain("family Sz := zs | ss (szPrev : Sz)\n"
               "family V : Sz -> Type 0 := vnil : V zs | vcons (vSize : Sz) (vTail : V vSize) : V (ss vSize) "
               "| vbad (badSize : Sz) (badTail : V badSize) (i : I) : V (ss badSize) "
               "[ ~i -> vcons badSize badTail, i -> badTail ]", "HIT_INDEX");
  ok &= domain("family Sz := zs | ss (szPrev : Sz)\n"
               "family V : Sz -> Type 0 := vnil | vcons (vSize : Sz) (vTail : V vSize) : V (ss vSize)", "HIT_INDEX");
  ok &= domain("family P0 : Q0 -> Type 0 := p0 : P0 q0 and Q0 := q0", "BLOCK_ORDER");
  /* hiit-wrong-head: the result of a constructor is not its family. */
  ok &= domain("family Sz := zs | ss (szPrev : Sz)\n"
               "family V : Sz -> Type 0 := vnil : Sz | vcons (vSize : Sz) (vTail : V vSize) : V (ss vSize)", "HIT_INDEX");
  ok &= domain("family W : Prop -> Type 0 := w0", "NAME_UNKNOWN");
  ok &= domain("family Ch := gen | adopt (adoptOf : Ch) (adoptBy : Rt adoptOf) "
               "and Rt : Ch -> Type 0 := rat (ratOf : Ch) : Rt ratOf", NULL);
  /* Index arguments are not constructor parameters in point or path cases. */
  ok &= domain("family Sz := zs | ss (pred : Sz)\n"
               "family V (A : Type 0) : Sz -> Type 0 := vn : V A zs "
               "| vc (item : A) : V A (ss zs) "
               "| seg (i : I) : V A zs [ ~i -> vn A, i -> vn A ]\n"
               "def result : Path Nat (fold 0 (fun a => a) refl (vc Nat 7)) 7 := refl", NULL);
  /* A transport's printed result must still inhabit the destination fibre. */
  ok &= normal_roundtrip_in("family Sz := zs | ss (pred : Sz)\n"
                            "family V (A : Type 0) : Sz -> Type 0 := vn : V A zs | vg (vgOf : A) : V A zs",
                            "V Nat zs", "transp (fun (i : I) => V Nat zs) i0 (vn Nat)");
  ok &= normal_roundtrip_in("family Sz := zs | ss (pred : Sz) "
                            "| edge (i : I) [ ~i -> zs, i -> ss zs ]\n"
                            "family V : Sz -> Type 0 := vn : V zs | vc : V (ss zs)",
                            "V (ss zs)", "transp (fun (i : I) => V (edge i)) i0 vn");
  ok &= normal_roundtrip_in("family Even := ez | es (oddPrev : Odd) "
                            "and Odd := os (evenPrev : Even)",
                            "Even", "transp (fun (i : I) => Even) i0 (es (os ez))");
  ok &= domain("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)\n"
               "def result : Nat := fold 0 (fun n => natAdd n 1) (es (os ez))", "TYPE_MISMATCH");
  /* Block folds print their targets before their constructor cases. */
  ok &= normal_roundtrip_in("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)",
                            "Even -> Nat", "fun x => fold Nat Unit 0 (fun u => 1) (fun n => unit) x");
  ok &= normal_roundtrip_in("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)",
                            "Odd -> Unit", "fun x => fold Nat Unit 0 (fun u => 1) (fun n => unit) x");
  ok &= domain("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)\n"
               "def point : Path Nat (fold Nat Unit 0 (fun u => 1) (fun n => unit) (es (os ez))) 1 := refl\n"
               "def other : Path Unit (fold Nat Unit 0 (fun u => 1) (fun n => unit) (os ez)) unit := refl", NULL);
  /* A recursive field of a sibling sort is typed at the target of that
     sort, and it folds at that sort. */
  ok &= domain("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)\n"
               "def one : Path Nat (fold Nat Unit 0 (fun (u : Unit) => 1) (fun (n : Nat) => unit) (es (os ez))) 1 := refl", NULL);
  ok &= domain("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)\n"
               "def two : Path (Option Nat) (fold (Option Nat) (Option Nat) (some 0) (fun (u : Option Nat) => bind u (fun (a : Nat) => natAdd a 1))"
               " (fun (n : Option Nat) => bind n (fun (a : Nat) => natAdd a 1)) (es (os ez))) (some 2) := refl", NULL);
  /* block-fold-extra: a block fold with an extra argument before the
     value. Without the arity test the extra argument is never read. */
  ok &= domain("family Even := ez | es (oddPrev : Odd) and Odd := os (evenPrev : Even)\n"
               "def bad : Nat := fold (Even -> Nat) Unit (fun (e : Even) => 0) (fun (u : Unit) => fun (e : Even) => 1) "
               "(fun (g : Even -> Nat) => unit) unit ez", "TYPE_MISMATCH");
  /* A path field over a sibling sort folds at that sibling. */
  ok &= domain("family Box := box (boxLeft : Item) (boxRight : Item) (boxPath : Path Item boxLeft boxRight) "
               "and Item := item\n"
               "def result : Path Nat 7 7 := fun (i : I) => "
               "fold Nat Unit (fun x y p => elim (fun (u : Unit) => Nat) 7 (p @ i)) unit (box item item refl)", NULL);
  /* Every sort's cases must use the scrutinee's parameter telescope. */
  ok &= domain("family F (m : Flag) := makeF (fValue : Nat) and G (n : Nat) := makeG\n"
               "def result : Unit := fold Unit Unit (fun x => unit) unit (makeG 7)", "TYPE_MISMATCH");
  ok &= domain("family F (m : Nat) := makeF (fValue : Nat) and G := makeG\n"
               "def result : Unit := fold Unit Unit (fun x => unit) unit makeG", "TYPE_MISMATCH");
  ok &= domain("family L (n : Nat) (e : Path Nat n n) := leftL (lValue : Nat) "
               "and R (n : Nat) (e : Path Nat n n) := rightR (rLeft : L n e)\n"
               "def firstL : Path Nat (fold Nat Unit (fun v => v) (fun v => unit) (leftL 7 refl 8)) 8 := refl\n"
               "def secondR : Path Unit (fold Nat Unit (fun v => v) (fun v => unit) (rightR 7 refl (leftL 7 refl 8))) unit := refl", NULL);
  /* Header folds must not see the zeroed, reserved constructor signatures. */
  ok &= domain("family A := a (n : Nat) and B (x : A) (y : fold Unit x) := b\n"
               "def value : B (a 0) unit := b (a 0) unit", "HIT_BOUNDARY");
  /* A later sort's universe propagates backwards through the block. */
  ok &= domain("family Low := low (high : High) and High := highCtor (big : Type 0)\n"
               "def small : Type 0 := Low", "TYPE_MISMATCH");
  ok &= domain("family Low := low (high : High) and High := highCtor (big : Type 0)\n"
               "def large : Type 1 := Low", NULL);
  ok &= domain("family F : ((G : Type 0) -> G -> G) -> Type 0 := "
               "mk (x : (T : Type 0) -> T -> T) : F x and G := g", NULL);
  ok &= domain("family F (G : Nat) : Path Nat G G -> Type 0 := mk (x : Path Nat G G) : F G x and G := g", NULL);
  ok &= domain("state State : Nat -> Type 0 := st (counter : Nat) : State counter", "REFUSE_STATE");
  ok &= domain("family U := u\n"
               "family T := pt (value : Nat) | arc (i : I) "
               "[ ~i -> pt (fold 0 u), i -> pt (fold 0 u) ]", NULL);
  ok &= domain("family T (n : Nat) := leafT (v : Nat) | nodeT (l : T 0) (r : T n)", "DOMAIN_FAMILY");
  /* A type constructor is a cell signature (S3, rule R1): a cons list, a
     value parameter, a parameter in no constructor, an and block and two
     generators for one parameter (open point QA1) are refused. */
  ok &= domain("family Lst (A : Type 0) := lstNil | lstCons (lstHead : A) (lstTail : Lst A)", "REFUSE_CELL");
  ok &= domain("family Tagged (A : Type 0) (n : Nat) := tagged (taggedOf : A)", "REFUSE_CELL");
  ok &= domain("family Phantom (A : Type 0) := phantom", "REFUSE_CELL");
  ok &= domain("family Even (A : Type 0) := ez | es (oddPrev : Odd A) and Odd (A : Type 0) := os (evenPrev : Even A)", "REFUSE_CELL");
  ok &= domain("family Two (A : Type 0) := genL (genLOf : A) | genR (genROf : A)", "REFUSE_CELL");
  /* Aliases and indices must not hide type arguments from the cell check. */
  ok &= domain("def U : Type 1 := Type 0\n"
               "family AliasList (A : U) := aliasNil | aliasCons (aliasHead : A) (aliasTail : AliasList A)", "REFUSE_CELL");
  ok &= domain("def U : Type 1 := Type 0\n"
               "family AliasCell (A : U) := aliasEta (aliasValue : A)", NULL);
  ok &= domain("family IndexedList : Type 0 -> Type 0 := idxNil (idxA : Type 0) : IndexedList idxA "
               "| idxCons (idxB : Type 0) (idxHead : idxB) (idxTail : IndexedList idxB) : IndexedList idxB", "REFUSE_CELL");
  ok &= domain("def U : Type 1 := Type 0\n"
               "family IndexedAlias : U -> Type 0 := indexedAlias (indexedType : U) : IndexedAlias indexedType", "REFUSE_CELL");
  ok &= domain("family Hkt (F : Type 0 -> Type 0) := hktNil | hktNode (hktValue : F Nat) (hktTail : Hkt F)", "REFUSE_CELL");
  ok &= domain("def Kind : Type 1 := Type 0 -> Type 0\n"
               "family HktAlias (F : Kind) := hktAliasNil", "REFUSE_CELL");
  /* Fixed operation labels are closed base data in a cell signature. */
  ok &= domain("family Labelled (A : Type 0) := labelledEta (labelledValue : A) "
               "| labelledNode (labelledTag : Nat) (labelledTail : Labelled A)", NULL);
  ok &= domain("family ClosedFn (A : Type 0) := closedEta (closedValue : A) "
               "| closedNode (closedLabel : (n : Nat) -> Path Nat n n) (closedTail : ClosedFn A)", NULL);
  ok &= domain("family BadLabel (A : Type 0) := badEta (badValue : A) "
               "| badNode (badLabel : Unit -> A) (badTail : BadLabel A)", "REFUSE_CELL");
  ok &= domain("family Wrapped (A : Type 0) := wrappedEta (wrappedValue : A) "
               "| wrappedNode (wrappedTail : Option (Wrapped A))", "REFUSE_CELL");
  ok &= domain("family F := makeF (field : Nat) (field : Flag)", "REFUSE_NAME");
  ok &= domain("family F := makeF (makeF : Nat)", "REFUSE_NAME");
  ok &= domain("family F := makeF (firstField : Nat) (secondField : Flag)", NULL);
  ok &= domain("family F := a (field : Nat) | b (field : Nat)", "REFUSE_NAME");
  ok &= domain("def s : Sum Nat Nat := inl 7\ndef bad : Sum Flag Nat := bind s (fun x => inr x)", "TYPE_MISMATCH");
  ok &= domain("family Lot (n : Nat) := makeLot (amount : Nat)\n"
               "def s : Sum Nat Nat := inl 0\n"
               "def f : (n : Nat) -> Nat -> Lot n := fun n x => makeLot n x\n"
               "def bad : (n : Nat) -> Lot n := first (pair (either f f s) 0)", "TYPE_MISMATCH");
  ok &= domain("def bad : Type 1 := Nat", "TYPE_MISMATCH");
  ok &= domain("def bad : Type 2 := Type 1", "TYPE_UNIVERSE");
  ok &= domain("family U := makeU (decode : Type 0)\ndef bad : Type 0 := U", "TYPE_MISMATCH");
  ok &= domain("family U := makeU (decode : Type 0)\nfamily W := makeW (wrapped : U)\ndef bad : Type 0 := W", "TYPE_MISMATCH");
  ok &= domain("family Box (A : Type 1) := box (unbox : A)\ndef bad : Type 0 := Box (Type 0)", "TYPE_MISMATCH");
  ok &= domain("family U := makeU (decode : Type 0)\ndef good : Type 1 := U", NULL);
  ok &= domain("def bad : Type 0 := Path (Type 0) Nat Nat", "TYPE_MISMATCH");
  ok &= domain("def good : Type 1 := Path (Type 0) Nat Nat", NULL);
  ok &= domain("def ConstNat : Nat -> Type 0 := fun n => Nat\n"
               "state State := makeState (count : Nat) (other : ConstNat count)\n"
               "def init : State := makeState 3 7\n"
               "def value : Path Nat (other init) 7 := refl", NULL);
  ok &= domain("state State := makeState (count : Nat) (proof : Path Nat count count)", "REFUSE_STATE");
  ok &= domain("family U := makeU (decode : Type 0)\n"
               "def bad : Type 0 := Path U (makeU Nat) (makeU Nat)", "TYPE_MISMATCH");
  ok &= domain("family U := makeU (decode : Type 0)\n"
               "def good : Type 1 := Path U (makeU Nat) (makeU Nat)", NULL);
  ok &= domain("family U := makeU (decode : Type 0)\n"
               "family W := makeW (proof : Path U (makeU Nat) (makeU Nat))\n"
               "def bad : Type 0 := W", "TYPE_MISMATCH");
  ok &= domain("family U := makeU (decode : Type 0)\n"
               "family W := makeW (proof : Path U (makeU Nat) (makeU Nat))\n"
               "def good : Type 1 := W", NULL);
  ok &= domain("def eta : (p : Prod Nat Nat) -> Path (Prod Nat Nat) (pair (first p) (second p)) p := fun p => refl", NULL);
  ok &= domain("def eta : (p : Sigma (n : Nat) (Path Nat n n)) -> Path (Sigma (n : Nat) (Path Nat n n)) (pack (witness p) (payload p)) p := fun p => refl", NULL);
  /* A cofamily is a cocell signature (S4, rule R1): one type parameter, one
     clause, exactly one observation `A`, and cofields `D A` or `E -> D A`
     with E closed. */
  ok &= domain("family Size := sz0 | szS (szPrev : Size)\n"
               "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)", NULL);
  ok &= domain("cofamily Tree (A : Type 0) := treeCorec (treeLabel : A) (treeLeft : Tree A) (treeRight : Tree A)", NULL);
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Br (A : Type 0) := brCorec (brHere : A) (brNext : Lab -> Br A)", NULL);
  ok &= domain("cofamily Ident (A : Type 0) := identCorec (identOut : A)", NULL);
  /* Closed labels are judged after normalization. Erased references to
     the parameter, self and earlier observations need no local context. */
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Br (A : Type 0) := brCorec (brHere : A) "
               "(brNext : ((fun (x : A) => Lab) brHere) -> Br A)\n"
               "def branch : Br Lab := brCorec Lab Lab (fun (s : Lab) => s) (fun (s : Lab) (e : Lab) => e) l0\n"
               "def branchLaw : Path Lab (brHere Lab (brNext Lab branch l1)) l1 := refl", NULL);
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Br (A : Type 0) := brCorec (brHere : A) "
               "(brNext : ((fun (T : Type 0) => Lab) (Br A)) -> Br A)", NULL);
  ok &= domain("cofamily Hi (A : Type 1) := hiCorec (hiOut : A) "
               "(hiType : Type 0 -> Hi A) (hiNat : Nat -> Hi A)", NULL);
  ok &= domain("cofamily Dep (A : Type 0) := depCorec (depOut : A) "
               "(depNext : Path A depOut depOut -> Dep A)", "REFUSE_CELL");
  ok &= domain("def U : Type 1 := Type 0\n"
               "cofamily AliasCo (A : U) := aliasCoCorec (aliasCoOut : A) (aliasCoNext : AliasCo A)", NULL);
  ok &= domain("cofamily Np := npCorec (npOut : Nat)", "REFUSE_CELL");
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Vp (n : Lab) := vpCorec (vpOut : Lab)", "REFUSE_CELL");
  ok &= domain("cofamily Tp (A : Type 0) (B : Type 0) := tpCorec (tpOut : A)", "REFUSE_CELL");
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Ix (A : Type 0) : Lab -> Type 0 := ixCorec (ixOut : A) : Ix A l0", "REFUSE_CELL");
  ok &= domain("cofamily Ab (A : Type 0) := abCorec (abOut : A) and Other := other", "REFUSE_CELL");
  ok &= domain("cofamily No (A : Type 0) := noCorec (noNext : No A)", "REFUSE_CELL");
  ok &= domain("cofamily Two (A : Type 0) := twoCorec (twoA : A) (twoB : A)", "REFUSE_CELL");
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Tg (A : Type 0) := tgCorec (tgOut : A) (tgTag : Lab)", "REFUSE_CELL");
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Dl (A : Type 0) := dlCorec (dlOut : A) (dlNext : Dl Lab)", "REFUSE_CELL");
  ok &= domain("cofamily Dd (A : Type 0) := ddCorec (ddOut : A) (ddNext : Dd (Dd A))", "REFUSE_CELL");
  ok &= domain("cofamily Ad (A : Type 0) := adCorec (adOut : A) (adNext : A -> Ad A)", "REFUSE_CELL");
  ok &= domain("cofamily Pf (A : Type 0) := pfCorec (pfOut : A) (pfT : Pf A) (pfP : Path (Pf A) pfT pfT)", "REFUSE_CELL");
  ok &= domain("cofamily Cf (A : Type 0) := cfCorec (cfOut : A) (cfNext : Cf A -> List (Cf A))", "REFUSE_CELL");
  ok &= domain("cofamily Lu (A : Type 0) := luCorec (luOut : A) (luNext : Type 0 -> Lu A)", "REFUSE_CELL");
  /* `sealed family` and `law def` are domain-only modifiers (S5, rule O7).
     A sealed family is a cell monad; a program cannot use either. */
  ok &= domain("sealed family Sl (A : Type 0) := slEta (slOf : A)", NULL);
  ok &= domain("sealed family Sl (A : Type 0) := slEta (slOf : A)\n"
               "law def slOut : (A : Type 0) -> Sl A -> A := fun A c => fold (fun a => a) c", NULL);
  ok &= domain("sealed family Sc := sc0 | sc1", "REFUSE_CELL");
  ok &= guest("sealed family Sl (A : Type 0) := slEta (slOf : A)", "REFUSE_DATA");
  ok &= guest("law def lawId : Type 1 := Type 0", "REFUSE_DATA");
  /* slOut is a law def (rule O7): a guest use outside a law type is
     refused, a use in a Trunc1 argument is not law-only, and a program
     def cannot take the name of the law def. */
  ok &= law_guest("def peek : Sl Size -> Size := fun c => slOut Size c", "REFUSE_LAW");
  ok &= law_guest("def settle : (c : Sl Size) -> Trunc1 (Path Size (slOut Size c) sz0) -> Size :=\n"
                  "  fun c p => sz0", NULL);
  ok &= law_guest("def slOut : Size := sz0", "REFUSE_NAME");
  /* The generated names are R4 names: a bisimulation name, a destructor
     name and a corecursor name that an earlier def holds are refused. */
  ok &= domain("def StrmBisim : Type 1 := Type 0\n"
               "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)", "REFUSE_NAME");
  ok &= domain("def strmTail : Type 1 := Type 0\n"
               "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)", "REFUSE_NAME");
  ok &= domain("def strmCorec : Type 1 := Type 0\n"
               "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)", "REFUSE_NAME");
  /* The elaborated destructors and corecursor compute by conversion: the
     head of the corecursor is the observation of the seed, and its tail is
     the corecursor at the next seed. */
  ok &= domain("family Size := sz0 | szS (szPrev : Size)\n"
               "cofamily Strm (A : Type 0) := strmCorec (strmHead : A) (strmTail : Strm A)\n"
               "def nats : Strm Size := strmCorec Size Size (fun (s : Size) => s) (fun (s : Size) => szS s) sz0\n"
               "def headLaw : Path Size (strmHead Size nats) sz0 := refl\n"
               "def tailLaw : Path (Strm Size) (strmTail Size nats) (strmCorec Size Size (fun (s : Size) => s) (fun (s : Size) => szS s) (szS sz0)) := refl", NULL);
  ok &= domain("family Lab := l0 | l1\n"
               "cofamily Br (A : Type 0) := brCorec (brHere : A) (brNext : Lab -> Br A)\n"
               "def brStep : Lab -> Lab -> Lab := fun (s : Lab) (e : Lab) => e\n"
               "def brAll : Br Lab := brCorec Lab Lab (fun (s : Lab) => s) brStep l0\n"
               "def brLaw : Path Lab (brHere Lab (brNext Lab brAll l1)) l1 := refl", NULL);
  ok &= normal_roundtrip("Nat -> (A : Type 0) -> A -> A",
    "fun (i0 : Nat) (A : Type 0) (a : A) => transp (fun (i : I) => A) (~i1) a");
  /* Guest mode (orbit-lang S3): a program with no kit name checks, and a Nat
     literal is a kit item. The second row passes in kit mode only if the mode
     is wrong. */
  ok &= guest("def keep : Sum Unit Unit -> Sum Unit Unit := fun c => c", NULL);
  ok &= guest("def three : Nat := 3", "REFUSE_KIT");
  if (ok) puts("domain regressions: passed");
  return ok ? 0 : 1;
}
