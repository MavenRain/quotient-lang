/* The type checker (see front/check.h). SHARED by the tcc kits.

   Checking is bidirectional. A term is checked against an expected type (the
   hint) or its type is inferred. Two types are equal when their normal forms
   are equal (front/eval.c). The checker writes core terms (front/core.h). */
#include "front/check.h"
#include "front/front.h"
#include "front/lexer.h"
#include "front/parser.h"

#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#define CHECK_DEPTH_LIMIT 2000u
#define SPINE_MAX 64u
#define SHOW_MAX 512u
#define NAMES_MAX 64u
#define UNIVERSE_MAX 2u
#define PRINT_MAX 65536u
#define NO_FAMILY UINT32_MAX
#define NO_DEF UINT32_MAX

#define FAIL(c, code, ...) diag_fail((c)->m->diag, (code), (c)->m->def, __VA_ARGS__)

typedef struct Scope Scope;
struct Scope {
  const char *name; /* NULL for the binder of `A -> B` */
  const Value *type;
  uint32_t level;
  const Scope *next;
};

typedef struct {
  Machine *m;
  const DeclList *decls;
  size_t decl_index;
  const Scope *scope; /* the innermost binder first */
  const Env *env;     /* a variable for each binder */
  uint32_t level;     /* the number of binders */
  unsigned depth;
  uint32_t eta_count;
  uint32_t self;       /* the first family of the block whose fields are checked, or NO_FAMILY */
  uint32_t self_count; /* the number of sorts of that block (S6) */
  /* A block fold (S6): the target of each sort, while a case type is made,
     or NULL. */
  const Value *const *fold_targets;
  uint32_t fold_first;
  uint32_t fold_count;
  /* The motive value while the case types of an elim over a domain family
     are built (S7 B1), else NULL. */
  const Value *elim_motive;
  uint32_t self_uses;  /* the uses of a sort of that block in the current field */
  /* The levels of the earlier point fields of the current field, from
     FIELD_BASE up to FIELD_TOP (S4 item 13), and the uses of them. */
  uint32_t field_base;
  uint32_t field_top;
  int field_dep;
  int field_rec;
  CheckMode mode; /* orbit-lang S3: guest or kit */
} Checker;

/* The visibility of a core name (orbit-lang S3). An INTERNAL name is a kit
   item outside the base span (PLAN section 4): only the trusted prelude
   scope and the kit mode resolve it. */
typedef enum {
  VIS_GUEST,
  VIS_INTERNAL,
  /* A cons-list name (S3, USER ruling Q-S3-5 (a), rule R1): the kit and
     the trusted scope use it (the host ABI); a guest use gives REFUSE_CELL. */
  VIS_CELL
} Vis;

typedef enum {
  RULE_TYPE0,
  RULE_TYPE1,
  RULE_TYPE2,
  RULE_INTERVAL,
  RULE_IEND,
  RULE_PATHP,
  RULE_PATH,
  RULE_VALUE0,
  RULE_PAIR,
  RULE_INJ,
  RULE_EMPTY,
  RULE_SOME,
  RULE_CONS,
  RULE_PACK,
  RULE_REFL,
  RULE_PART,
  RULE_SIGMA_PART,
  RULE_EITHER,
  RULE_OPTION,
  RULE_ELIM,
  RULE_PURE,
  RULE_MAP,
  RULE_BIND,
  RULE_STEP_LET,
  RULE_FILTER,
  RULE_FOLD,
  RULE_UNFOLD,
  RULE_SYM,
  RULE_CONG,
  RULE_FUNEXT,
  RULE_TRANSP,
  RULE_HCOMP,
  RULE_NAT2,
  RULE_AMOUNT2,
  RULE_LEN, /* S3: len A r (survey section 7) */
  RULE_VALUE_COUNT, /* S2: valueCount A v a (USER ruling Q-S2-5 (a)) */
  RULE_FLAG_IF,
  RULE_NONZERO,       /* S3: NonZero Nat */
  RULE_NONZERO_OF,    /* nonZero x */
  RULE_NONZERO_VALUE, /* nonZeroValue x */
  RULE_DIV,           /* natDiv, natMod: a NonZero divisor */
  RULE_KMAP,
  RULE_KMAP_GET,
  RULE_KMAP_SET,
  RULE_FIN,
  RULE_FIN_OP,
  RULE_GLUE,
  RULE_GLUE_ELEM,
  RULE_UNGLUE,
} Rule;

typedef struct {
  const char *name;
  uint32_t arity; /* fold: the least number of arguments */
  Rule rule;
  Op op;
  Op result;     /* VALUE0, NAT2: the result type. EMPTY, INJ: the type former. */
  uint32_t part; /* INJ, PART, SIGMA_PART: 0 or 1 */
  Vis vis;
} Builtin;

static const Builtin BUILTINS[] = {
  {"Nat", 0, RULE_TYPE0, OP_NAT, OP_NAT, 0, VIS_INTERNAL},
  {"Flag", 0, RULE_TYPE0, OP_FLAG, OP_NAT, 0, VIS_INTERNAL},
  {"Unit", 0, RULE_TYPE0, OP_UNIT, OP_NAT, 0, VIS_GUEST},
  {"Prod", 2, RULE_TYPE2, OP_PROD, OP_NAT, 0, VIS_GUEST},
  {"Sum", 2, RULE_TYPE2, OP_SUM, OP_NAT, 0, VIS_GUEST},
  {"Option", 1, RULE_TYPE1, OP_OPTION, OP_NAT, 0, VIS_GUEST},
  {"List", 1, RULE_TYPE1, OP_LIST, OP_NAT, 0, VIS_CELL},
  {"Fin", 1, RULE_FIN, OP_FIN, OP_NAT, 0, VIS_INTERNAL},
  {"finAdd", 3, RULE_FIN_OP, OP_FIN_ADD, OP_FIN, 0, VIS_INTERNAL},
  {"finNeg", 2, RULE_FIN_OP, OP_FIN_NEG, OP_FIN, 0, VIS_INTERNAL},
  {"I", 0, RULE_INTERVAL, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"i0", 0, RULE_IEND, OP_INTERVAL, OP_INTERVAL, 0, VIS_GUEST},
  {"i1", 0, RULE_IEND, OP_INTERVAL, OP_INTERVAL, 1, VIS_GUEST},
  {"PathP", 3, RULE_PATHP, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"Path", 3, RULE_PATH, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"unit", 0, RULE_VALUE0, OP_UNIT_VAL, OP_UNIT, 0, VIS_GUEST},
  {"flagYes", 0, RULE_VALUE0, OP_FLAG_YES, OP_FLAG, 0, VIS_INTERNAL},
  {"flagNo", 0, RULE_VALUE0, OP_FLAG_NO, OP_FLAG, 0, VIS_INTERNAL},
  {"pair", 2, RULE_PAIR, OP_PAIR, OP_PROD, 0, VIS_GUEST},
  {"inl", 1, RULE_INJ, OP_INL, OP_SUM, 0, VIS_GUEST},
  {"inr", 1, RULE_INJ, OP_INR, OP_SUM, 1, VIS_GUEST},
  {"none", 0, RULE_EMPTY, OP_NONE, OP_OPTION, 0, VIS_GUEST},
  {"nil", 0, RULE_EMPTY, OP_NIL, OP_LIST, 0, VIS_CELL},
  {"some", 1, RULE_SOME, OP_SOME, OP_OPTION, 0, VIS_GUEST},
  {"cons", 2, RULE_CONS, OP_CONS, OP_LIST, 0, VIS_CELL},
  {"pack", 2, RULE_PACK, OP_PACK, OP_NAT, 0, VIS_GUEST},
  {"refl", 0, RULE_REFL, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"first", 1, RULE_PART, OP_FIRST, OP_PROD, 0, VIS_GUEST},
  {"second", 1, RULE_PART, OP_SECOND, OP_PROD, 1, VIS_GUEST},
  {"witness", 1, RULE_SIGMA_PART, OP_WITNESS, OP_NAT, 0, VIS_GUEST},
  {"payload", 1, RULE_SIGMA_PART, OP_PAYLOAD, OP_NAT, 1, VIS_GUEST},
  {"either", 3, RULE_EITHER, OP_EITHER, OP_SUM, 0, VIS_GUEST},
  {"option", 3, RULE_OPTION, OP_OPTION_ELIM, OP_OPTION, 0, VIS_GUEST},
  {"elim", 3, RULE_ELIM, OP_ELIM, OP_SUM, 0, VIS_GUEST},
  {"pure", 1, RULE_PURE, OP_PURE, OP_NAT, 0, VIS_GUEST},
  {"map", 2, RULE_MAP, OP_MAP, OP_NAT, 0, VIS_GUEST},
  {"bind", 2, RULE_BIND, OP_BIND, OP_NAT, 0, VIS_GUEST},
  {"filter", 2, RULE_FILTER, OP_FILTER, OP_NAT, 0, VIS_GUEST},
  {"fold", 2, RULE_FOLD, OP_FOLD_NAT, OP_NAT, 0, VIS_GUEST},
  {"unfold", 3, RULE_UNFOLD, OP_UNFOLD, OP_LIST, 0, VIS_CELL},
  {"sym", 1, RULE_SYM, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"cong", 2, RULE_CONG, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"funExt", 1, RULE_FUNEXT, OP_INTERVAL, OP_NAT, 0, VIS_GUEST},
  {"transp", 3, RULE_TRANSP, OP_TRANSP, OP_NAT, 0, VIS_GUEST},
  {"hcomp", 4, RULE_HCOMP, OP_HCOMP, OP_NAT, 0, VIS_GUEST},
  {"Glue", 3, RULE_GLUE, OP_GLUE, OP_NAT, 0, VIS_GUEST},
  {"glue", 2, RULE_GLUE_ELEM, OP_GLUE_ELEM, OP_NAT, 0, VIS_GUEST},
  {"unglue", 1, RULE_UNGLUE, OP_UNGLUE, OP_NAT, 0, VIS_GUEST},
  {"natAdd", 2, RULE_NAT2, OP_NAT_ADD, OP_OPTION, 0, VIS_INTERNAL},
  {"natSub", 2, RULE_NAT2, OP_NAT_SUB, OP_NAT, 0, VIS_INTERNAL},
  {"natEq", 2, RULE_NAT2, OP_NAT_EQ, OP_FLAG, 0, VIS_INTERNAL},
  {"natLe", 2, RULE_NAT2, OP_NAT_LE, OP_FLAG, 0, VIS_INTERNAL},
  {"natSucc", 1, RULE_NAT2, OP_NAT_SUCC, OP_NAT, 0, VIS_INTERNAL},
  {"flagIf", 3, RULE_FLAG_IF, OP_FLAG_IF, OP_FLAG, 0, VIS_INTERNAL},
  {"Map", 2, RULE_KMAP, OP_KMAP, OP_NAT, 0, VIS_INTERNAL},
  {"mapEmpty", 0, RULE_EMPTY, OP_KMAP_OF, OP_KMAP, 0, VIS_INTERNAL},
  {"mapGet", 2, RULE_KMAP_GET, OP_KMAP_GET, OP_KMAP, 0, VIS_INTERNAL},
  {"mapSet", 3, RULE_KMAP_SET, OP_KMAP_SET, OP_KMAP, 0, VIS_INTERNAL},
  {"natDiv", 2, RULE_DIV, OP_NAT_DIV, OP_NAT, 0, VIS_INTERNAL},
  {"natMod", 2, RULE_DIV, OP_NAT_MOD, OP_NAT, 0, VIS_INTERNAL},
  {"NonZero", 1, RULE_NONZERO, OP_NONZERO, OP_NAT, 0, VIS_INTERNAL},
  {"nonZero", 1, RULE_NONZERO_OF, OP_NONZERO_OF, OP_OPTION, 0, VIS_INTERNAL},
  {"nonZeroValue", 1, RULE_NONZERO_VALUE, OP_NONZERO_VALUE, OP_NAT, 0, VIS_INTERNAL},
  {"len", 2, RULE_LEN, OP_FM_LEN, OP_NAT, 0, VIS_GUEST},
  {"Amount", 0, RULE_TYPE0, OP_AMOUNT, OP_NAT, 0, VIS_GUEST},
  {"amountAdd", 2, RULE_AMOUNT2, OP_AMOUNT_ADD, OP_OPTION, 0, VIS_GUEST},
  {"amountSub", 2, RULE_AMOUNT2, OP_AMOUNT_SUB, OP_OPTION, 0, VIS_GUEST},
  {"valueCount", 3, RULE_VALUE_COUNT, OP_VALUE_COUNT, OP_AMOUNT, 0, VIS_GUEST},
  {"step#let", 2, RULE_STEP_LET, OP_BIND, OP_NAT, 0, VIS_INTERNAL},
};

#define BUILTIN_COUNT ((uint32_t)(sizeof BUILTINS / sizeof BUILTINS[0]))

/* Names that no declaration can take (rule R4). Prop and SProp are
   reserved because proof irrelevance is prohibited (orbit-lang S1
   ruling): no declaration can give a type the name of a Prop-like
   universe. */
static const char *const RESERVED[] = {"Bool", "Text", "Prop", "SProp"};

/* Time words (S3, O3): no declaration can take one and no name can use
   one (REFUSE_TIME). A program counts operations instead. */
static const char *const TIME_WORDS[] = {"now", "block", "timestamp", "time", "clock", "epoch"};

#define TIME_HINT "%s is a time word; count operations: a position is `len r` (an OpPos) and a deadline is a count of later operations"

static int time_word(const char *name) {
  size_t i;
  for (i = 0; i < sizeof TIME_WORDS / sizeof TIME_WORDS[0]; i++) {
    if (strcmp(TIME_WORDS[i], name) == 0)
      return 1;
  }
  return 0;
}

/* REFUSE_NOT_IN_DESIGN (quotient-lang S1, PLAN section 7), path 1. The
   rows X4 and X10 of PLAN section 4 are DROP rows: no declaration form and
   no binder can take one of these names. */
typedef struct {
  const char *name;
  const char *row;
  const char *why;
} DroppedName;

#define DROP_X4 "it is no path on histories: \"invalid\" depends on the state, and replay counts"
#define DROP_X10 "it has no finite value, and Forks and ~cons have no definition; agreement is Compatible (X9)"

static const DroppedName DROPPED[] = {
  {"absorb", "X4", DROP_X4},
  {"absorption", "X4", DROP_X4},
  {"GenConsensus", "X10", DROP_X10},
  {"CanonicalChain", "X10", DROP_X10},
  {"Forks", "X10", DROP_X10},
  {"colimit", "X10", DROP_X10},
  {"runColimit", "X10", DROP_X10}
};

#define DROPPED_HINT "%s is a name of the DROP row %s of PLAN section 4; %s"

static const DroppedName *dropped_name(const char *name) {
  size_t i;
  for (i = 0; i < sizeof DROPPED / sizeof DROPPED[0]; i++) {
    if (strcmp(DROPPED[i].name, name) == 0)
      return &DROPPED[i];
  }
  return NULL;
}

/* REFUSE_NOT_IN_DESIGN, path 2: the base sorts that PLAN section 4 admits
   (the types of X1 to X21), the design parameters and the instances of
   PLAN section 3. An opaque base sort (an axiom of a universe type) with
   another name is refused. Other axioms keep REFUSE_AXIOM (Q-S1-2 (a)). */
static const char *const ADMITTED[] = {
  "Body", "Witness", "Authorized", "AuthTx", "Ind", "Trace", "Eff",
  "Blockchain", "Ledger", "Compatible", "Bag", "Value", "Balance", "Delta",
  "Balanced", "UTxO", "Sig", "QC", "Pfin", "Mempool", "FinMap", "Digest",
  "Valid", "D",
  "Asset", "Owner", "Key", "Val", "Node", "OutRef", "Output", "Query",
  "Answer", "Amount", "State",
  "Footprint", "History", "Net", "Signers", "Sigs", "Store", "Maybe"
};

static int admitted_name(const char *name) {
  size_t i;
  for (i = 0; i < sizeof ADMITTED / sizeof ADMITTED[0]; i++) {
    if (strcmp(ADMITTED[i], name) == 0)
      return 1;
  }
  return 0;
}

typedef enum {
  HEAD_TERM, /* a local, a definition or another term: plain application */
  HEAD_FAMILY,
  HEAD_CTOR,
  HEAD_PROJ,
  HEAD_BUILTIN
} HeadKind;

typedef struct {
  HeadKind kind;
  uint32_t index; /* FAMILY: the family. CTOR, PROJ: the constructor. */
  uint32_t field; /* PROJ: the field number */
  const Builtin *builtin;
} Head;

/* One application of a core name to the arguments of a spine. */
typedef struct {
  Checker *c;
  const Builtin *b;
  const Term *const *args;
  uint32_t argc;      /* the arguments in the spine */
  const Value *hint;  /* the expected type of the result, or NULL */
  const Value *outer; /* the expected type of the whole spine, or NULL */
  uint32_t used;      /* the arguments that the core name takes */
  const Value *type;  /* the type of the result */
} Call;

static const Core *nul(int failed) {
  (void)failed;
  return NULL;
}

static const Value *vnul(int failed) {
  (void)failed;
  return NULL;
}

static Core *new_core(Checker *c, CoreKind kind) {
  Core *k = arena_alloc(c->m->arena, sizeof *k);
  if (k == NULL) {
    FAIL(c, "OOM", "out of memory");
    return NULL;
  }
  k->kind = kind;
  return k;
}

static const Core *core_index(Checker *c, CoreKind kind, uint32_t index) {
  Core *k = new_core(c, kind);
  if (k != NULL)
    k->index = index;
  return k;
}

static const Core *core_leaf(Checker *c, CoreKind kind, uint64_t nat) {
  Core *k = new_core(c, kind);
  if (k != NULL)
    k->nat = nat;
  return k;
}

static const Core *core_bind(Checker *c, CoreKind kind, const char *name, const Core *a, const Core *b) {
  Core *k;
  if (b == NULL || (a == NULL && kind != CORE_LAM && kind != CORE_PLAM))
    return NULL;
  k = new_core(c, kind);
  if (k == NULL)
    return NULL;
  k->name = name;
  k->a = a;
  k->b = b;
  return k;
}

static const Core *core_app(Checker *c, const Core *f, const Core *x) {
  Core *k;
  if (f == NULL || x == NULL)
    return NULL;
  k = new_core(c, CORE_APP);
  if (k == NULL)
    return NULL;
  k->a = f;
  k->b = x;
  return k;
}

/* CORE_PATHP (the line B) and CORE_PAPP (the path A at the interval B), with
   the ends E0 and E1. */
static const Core *core_ends(Checker *c, CoreKind kind, const char *name, const Core *a, const Core *b, const Core *e0, const Core *e1) {
  const Core **ends;
  Core *k;
  if (b == NULL || e0 == NULL || e1 == NULL || (a == NULL && kind != CORE_PATHP))
    return NULL;
  ends = arena_alloc(c->m->arena, 2u * sizeof *ends);
  if (ends == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  k = new_core(c, kind);
  if (k == NULL)
    return NULL;
  ends[0] = e0;
  ends[1] = e1;
  k->name = name;
  k->a = a;
  k->b = b;
  k->args = ends;
  k->argc = 2;
  return k;
}

/* An interval term: CORE_INEG (A), CORE_IMEET and CORE_IJOIN (A, B). */
static const Core *core_iop(Checker *c, CoreKind kind, const Core *a, const Core *b) {
  Core *k;
  if (a == NULL || (b == NULL && kind != CORE_INEG))
    return NULL;
  k = new_core(c, kind);
  if (k != NULL) {
    k->a = a;
    k->b = b;
  }
  return k;
}

static const Core *core_op(Checker *c, Op op, uint32_t inst, uint32_t field, const Core *const *args, uint32_t n) {
  const Core **copy = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *copy);
  Core *k;
  uint32_t i;
  if (copy == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < n; i++) {
    if (args[i] == NULL)
      return NULL;
    copy[i] = args[i];
  }
  k = new_core(c, CORE_OP);
  if (k == NULL)
    return NULL;
  k->op = op;
  k->inst = inst;
  k->field = field;
  k->args = copy;
  k->argc = n;
  return k;
}

static const Core *op3(Checker *c, Op op, uint32_t inst, uint32_t n, const Core *a, const Core *b, const Core *x) {
  const Core *args[3];
  args[0] = a;
  args[1] = b;
  args[2] = x;
  return core_op(c, op, inst, 0, args, n);
}

static const Value *tyop(Checker *c, Op op, uint32_t n, const Value *a, const Value *b, const Value *x) {
  return val_make(c->m, op, 0, n, a, b, x);
}

static const Value *nat_type(Checker *c) {
  return tyop(c, OP_NAT, 0, NULL, NULL, NULL);
}

static const Value *flag_type(Checker *c) {
  return tyop(c, OP_FLAG, 0, NULL, NULL, NULL);
}

/* The sort I: the type of an interval term, never a type itself. */
static const Value *interval_type(Checker *c) {
  return tyop(c, OP_INTERVAL, 0, NULL, NULL, NULL);
}

/* The value of the core term K in the current context. */
static const Value *here(Checker *c, const Core *k) {
  return k == NULL ? NULL : eval_core(c->m, c->env, k);
}

/* V in the surface syntax, for a diagnostic. */
static const char *show(Checker *c, const Value *v) {
  const char *names[NAMES_MAX];
  const Scope *s;
  char *buf = arena_alloc(c->m->arena, SHOW_MAX);
  uint32_t count = c->level < NAMES_MAX ? c->level : NAMES_MAX;
  for (s = c->scope; s != NULL; s = s->next) {
    if (s->level < NAMES_MAX)
      names[s->level] = s->name != NULL ? s->name : "_";
  }
  if (buf == NULL || v == NULL)
    return "?";
  value_print(c->m, names, count, v, buf, SHOW_MAX);
  return buf;
}

static int push_value(Checker *c, const char *name, const Value *type, const Value *value) {
  Scope *s;
  const Env *e;
  const DroppedName *x = name != NULL ? dropped_name(name) : NULL;
  if (x != NULL)
    return FAIL(c, "REFUSE_NOT_IN_DESIGN", DROPPED_HINT, name, x->row, x->why);
  if (name != NULL && time_word(name))
    return FAIL(c, "REFUSE_TIME", TIME_HINT, name);
  s = arena_alloc(c->m->arena, sizeof *s);
  e = env_push(c->m, c->env, value);
  if (type == NULL || value == NULL || s == NULL || e == NULL)
    return c->m->diag->set ? 0 : FAIL(c, "OOM", "out of memory");
  s->name = name;
  s->type = type;
  s->level = c->level;
  s->next = c->scope;
  c->scope = s;
  c->env = e;
  c->level++;
  return 1;
}

static int push(Checker *c, const char *name, const Value *type) {
  return push_value(c, name, type, val_var(c->m, c->level));
}

/* An interval binder: its value is an interval variable, not a neutral. */
static int push_interval(Checker *c, const char *name) {
  return push_value(c, name, interval_type(c), val_ivar(c->m, c->level));
}

static void pop(Checker *c) {
  c->scope = c->scope->next;
  c->env = c->env->next;
  c->level--;
}

/* 1 when a term of type FOUND can stand where WANT is expected.
   Universes are not cumulative (former F14). */
static int expect(Checker *c, const Value *found, const Value *want) {
  if (found == NULL || want == NULL)
    return 0;
  if (conv_values(c->m, c->level, found, want))
    return 1;
  return FAIL(c, "TYPE_MISMATCH", "expected a term of type %s, found a term of type %s", show(c, want), show(c, found));
}

static const Scope *find_local(const Checker *c, const char *name) {
  const Scope *s;
  for (s = c->scope; s != NULL; s = s->next) {
    if (s->name != NULL && strcmp(s->name, name) == 0)
      return s;
  }
  return NULL;
}

static uint32_t find_def(const Machine *m, const char *name) {
  uint32_t i;
  for (i = 0; i < m->def_count; i++) {
    if (strcmp(m->defs[i].name, name) == 0)
      return i;
  }
  return NO_DEF;
}

/* 1 when ANN is the sort I: the name I, not taken by a local or a
   definition. Only a binder annotation can name I. */
static int is_interval(const Checker *c, const Term *ann) {
  return ann != NULL && ann->kind == TERM_VAR && strcmp(ann->name, "I") == 0 && find_local(c, ann->name) == NULL && find_def(c->m, ann->name) == NO_DEF;
}

/* An environment that binds VALS in order: the last one is index 0. */
static const Env *env_of(Checker *c, const Value *const *vals, uint32_t n) {
  const Env *e = NULL;
  uint32_t i;
  for (i = 0; i < n; i++)
    e = env_push(c->m, e, vals[i]);
  return e;
}

/* The value of K, a term under one interval binder, with R for the binder. */
static const Value *at(Checker *c, const Core *k, const Value *r) {
  const Env *e = env_push(c->m, c->env, r);
  return k == NULL || e == NULL ? NULL : eval_core(c->m, e, k);
}

static int end_fail(Checker *c, int uip, const char *side, const Value *found, const Value *want) {
  if (uip)
    return FAIL(c, "PATH_UIP", "the path at %s is %s, but the type needs %s; these ends are paths, and only a rule of uniqueness of identity proofs can make them equal (rule R9)", side, show(c, found), show(c, want));
  return FAIL(c, "PATH_END", "the path at %s is %s, but the type needs %s", side, show(c, found), show(c, want));
}

/* The end check of a path against the path type E: V0 and V1 are its
   values at i0 and i1. */
static int path_ends(Checker *c, const Value *e, const Value *v0, const Value *v1) {
  const Value *ends = closure_apply(c->m, e, val_iend(c->m, 0));
  int uip = ends != NULL && ends->kind == VAL_PATHP;
  if (v0 == NULL || v1 == NULL)
    return 0;
  if (!conv_values(c->m, c->level, v0, e->args[0]))
    return end_fail(c, uip, "i0", v0, e->args[0]);
  return conv_values(c->m, c->level, v1, e->args[1]) ? 1 : end_fail(c, uip, "i1", v1, e->args[1]);
}

static const Core *elab(Checker *c, const Term *t, const Value *hint, const Value **type);
static const Core *check_lam(Checker *c, const Term *t, const Value *hint, const Value **type);
static const Core *checked_annotation(Checker *c, const Term *ann, const Value *dom);

static const Core *check(Checker *c, const Term *t, const Value *want) {
  const Value *type = NULL;
  return want == NULL ? NULL : elab(c, t, want, &type);
}

static const Core *infer(Checker *c, const Term *t, const Value **type) {
  *type = NULL;
  return elab(c, t, NULL, type);
}

/* infer, but a failure leaves no diagnostic. */
static const Core *try_infer(Checker *c, const Term *t, const Value **type) {
  Diag saved = *c->m->diag;
  const Core *k = infer(c, t, type);
  if (k == NULL)
    *c->m->diag = saved;
  return k;
}

static const Core *check_type(Checker *c, const Term *t, uint64_t *level) {
  const Value *type = NULL;
  const Core *k = infer(c, t, &type);
  if (k == NULL)
    return NULL;
  if (type == NULL || type->kind != VAL_UNIV)
    return nul(FAIL(c, "TYPE_MISMATCH", "expected a type, found a term of type %s", show(c, type)));
  *level = type->nat;
  return k;
}

/* Compares the inferred *TYPE with HINT. */
static const Core *finish(Checker *c, const Core *k, const Value *hint, const Value **type) {
  if (k == NULL || *type == NULL)
    return NULL;
  if (hint != NULL && !expect(c, *type, hint))
    return NULL;
  *type = hint != NULL ? hint : *type;
  return k;
}

/* 1 when T is Option A, List A or Sum E A. *ELEM is A. */
static int carrier_of(const Value *t, Carrier *carrier, const Value **elem) {
  if (val_is(t, OP_OPTION) || val_is(t, OP_LIST)) {
    *carrier = val_is(t, OP_OPTION) ? CARRIER_OPTION : CARRIER_LIST;
    *elem = t->args[0];
    return 1;
  }
  if (!val_is(t, OP_SUM))
    return 0;
  *carrier = CARRIER_SUM;
  *elem = t->args[1];
  return 1;
}

/* SHAPE (Option, List or Sum E) with the element ELEM. */
static const Value *carried(Checker *c, const Value *shape, const Value *elem) {
  if (shape == NULL)
    return NULL;
  return val_is(shape, OP_SUM) ? tyop(c, OP_SUM, 2, shape->args[0], elem, NULL) : tyop(c, shape->op, 1, elem, NULL, NULL);
}

/* Checks T as a function from DOM. *RESULT is WANT, or the result type that
   T infers when WANT is NULL. */
static const Core *fn_into(Checker *c, const Term *t, const Value *dom, const Value *want, const Value **result) {
  const Value *ft = NULL;
  const Core *f;
  if (want != NULL) {
    *result = want;
    return check(c, t, val_arrow(c->m, dom, want));
  }
  f = infer(c, t, &ft);
  if (f == NULL)
    return NULL;
  if (ft == NULL || ft->kind != VAL_PI)
    return nul(FAIL(c, "TYPE_NOT_FUNCTION", "expected a function, found a term of type %s", show(c, ft)));
  *result = closure_apply(c->m, ft, val_var(c->m, c->level));
  /* Check dependence before the result leaves its binder. */
  if (!conv_values(c->m, c->level + 2u, *result,
                   closure_apply(c->m, ft, val_var(c->m, c->level + 1u))))
    return nul(FAIL(c, "TYPE_MISMATCH", "this operation needs a function with a non-dependent result type"));
  return expect(c, ft, val_arrow(c->m, dom, *result)) ? f : NULL;
}

/* The argument type of the function T, from its binder or its type. */
static const Value *lam_domain(Checker *c, const Term *t) {
  uint64_t level = 0;
  const Value *ft = NULL;
  if (t->kind == TERM_LAM && t->left != NULL)
    return here(c, check_type(c, t->left, &level));
  return try_infer(c, t, &ft) != NULL && ft != NULL && ft->kind == VAL_PI ? ft->dom : NULL;
}

/* The carried argument ARG of map, bind or filter. When ARG does not infer
   (`inr 3`), its type comes from the expected type and from the binder of
   the function FN. */
static const Core *carried_arg(Call *k, const Term *arg, const Term *fn, const Value **type) {
  Checker *c = k->c;
  Carrier carrier = CARRIER_OPTION;
  const Value *elem = NULL;
  const Value *dom;
  const Core *x = try_infer(c, arg, type);
  if (x != NULL)
    return x;
  if (!carrier_of(k->hint, &carrier, &elem))
    return infer(c, arg, type);
  dom = lam_domain(c, fn);
  if (dom == NULL)
    return infer(c, arg, type);
  *type = carried(c, k->hint, dom);
  return check(c, arg, *type);
}

static const Core *need_type(Call *k, const char *what) {
  return nul(FAIL(k->c, "TYPE_INFER", "%s needs a declared type %s here", k->b->name, what));
}

static const Core *not_carrier(Call *k, const Value *type) {
  return nul(FAIL(k->c, "TYPE_MISMATCH", "%s needs a value of type Option A, List A or Sum E A, found a term of type %s", k->b->name, show(k->c, type)));
}

/* Infers the argument I of K as a path. */
static const Core *infer_path(Call *k, uint32_t i, const Value **type) {
  const Core *p = infer(k->c, k->args[i], type);
  if (p == NULL)
    return NULL;
  return *type != NULL && (*type)->kind == VAL_PATHP ? p : nul(FAIL(k->c, "TYPE_MISMATCH", "%s needs a path of type PathP L a b, found a term of type %s", k->b->name, show(k->c, *type)));
}

static const Core *rule_type1(Call *k) {
  uint64_t level = 0;
  const Core *a = check_type(k->c, k->args[0], &level);
  k->type = val_univ(k->c->m, level);
  return op3(k->c, k->b->op, 0, 1, a, NULL, NULL);
}

static const Core *rule_type2(Call *k) {
  uint64_t la = 0;
  uint64_t lb = 0;
  const Core *a = check_type(k->c, k->args[0], &la);
  const Core *b = a == NULL ? NULL : check_type(k->c, k->args[1], &lb);
  k->type = val_univ(k->c->m, la > lb ? la : lb);
  return op3(k->c, k->b->op, 0, 2, a, b, NULL);
}

/* The line of PathP: `fun (i : I) => A` or `fun i => A`, with A a type of
   *LEVEL. The core is A, under the interval binder. */
static const Core *check_line(Checker *c, const Term *t, uint64_t *level) {
  const Core *body;
  if (t->kind != TERM_LAM || (t->left != NULL && !is_interval(c, t->left)))
    return nul(FAIL(c, "TYPE_MISMATCH", "the line of PathP must be an interval abstraction fun (i : I) => A"));
  if (!push_interval(c, t->name))
    return NULL;
  body = check_type(c, t->right, level);
  pop(c);
  return body;
}

/* PathP (fun i => A) a b, with a : A[i0] and b : A[i1] (rule R12). The
   level of A is the level of the path type. */
static const Core *rule_pathp(Call *k) {
  Checker *c = k->c;
  uint64_t level = 0;
  const Core *line = check_line(c, k->args[0], &level);
  const Core *a = line == NULL ? NULL : check(c, k->args[1], at(c, line, val_iend(c->m, 0)));
  const Core *b = a == NULL ? NULL : check(c, k->args[2], at(c, line, val_iend(c->m, 1)));
  k->type = val_univ(c->m, level);
  return core_ends(c, CORE_PATHP, k->args[0]->name, NULL, line, a, b);
}

/* Path A a b is PathP (fun _ => A) a b. */
static const Core *rule_path(Call *k) {
  Checker *c = k->c;
  uint64_t level = 0;
  const Core *t = check_type(c, k->args[0], &level);
  const Value *tv = here(c, t);
  const Core *a = check(c, k->args[1], tv);
  const Core *b = a == NULL ? NULL : check(c, k->args[2], tv);
  k->type = val_univ(c->m, level);
  return core_ends(c, CORE_PATHP, "_", NULL, b == NULL ? NULL : quote_value(c->m, c->level + 1u, tv), a, b);
}

static const Core *rule_pair(Call *k) {
  Checker *c = k->c;
  const Value *ta = val_is(k->hint, OP_PROD) ? k->hint->args[0] : NULL;
  const Value *tb = val_is(k->hint, OP_PROD) ? k->hint->args[1] : NULL;
  const Core *a = ta != NULL ? check(c, k->args[0], ta) : infer(c, k->args[0], &ta);
  const Core *b = a == NULL ? NULL : (tb != NULL ? check(c, k->args[1], tb) : infer(c, k->args[1], &tb));
  k->type = tyop(c, OP_PROD, 2, ta, tb, NULL);
  return op3(c, OP_PAIR, 0, 2, a, b, NULL);
}

static const Core *rule_inj(Call *k) {
  if (!val_is(k->hint, OP_SUM))
    return need_type(k, "Sum A B");
  k->type = k->hint;
  return op3(k->c, k->b->op, 0, 1, check(k->c, k->args[0], k->hint->args[k->b->part]), NULL, NULL);
}

static const Core *rule_empty(Call *k) {
  if (!val_is(k->hint, k->b->result))
    return need_type(k, k->b->result == OP_OPTION ? "Option A" : k->b->result == OP_KMAP ? "Map K V" : "List A");
  k->type = k->hint;
  return op3(k->c, k->b->op, 0, 0, NULL, NULL, NULL);
}

static const Core *rule_some(Call *k) {
  Checker *c = k->c;
  const Value *a = val_is(k->hint, OP_OPTION) ? k->hint->args[0] : NULL;
  const Core *x = a != NULL ? check(c, k->args[0], a) : infer(c, k->args[0], &a);
  k->type = tyop(c, OP_OPTION, 1, a, NULL, NULL);
  return op3(c, OP_SOME, 0, 1, x, NULL, NULL);
}

static const Core *rule_cons(Call *k) {
  Checker *c = k->c;
  const Value *a = val_is(k->hint, OP_LIST) ? k->hint->args[0] : NULL;
  const Core *x = a != NULL ? check(c, k->args[0], a) : infer(c, k->args[0], &a);
  const Value *list = tyop(c, OP_LIST, 1, a, NULL, NULL);
  const Core *xs = x == NULL ? NULL : check(c, k->args[1], list);
  k->type = list;
  return op3(c, OP_CONS, 0, 2, x, xs, NULL);
}

static const Core *rule_pack(Call *k) {
  Checker *c = k->c;
  const Value *s = k->hint;
  const Core *w;
  const Core *p;
  if (s == NULL || s->kind != VAL_SIGMA)
    return need_type(k, "Sigma (x : A) B");
  w = check(c, k->args[0], s->dom);
  p = w == NULL ? NULL : check(c, k->args[1], closure_apply(c->m, s, here(c, w)));
  k->type = s;
  return op3(c, OP_PACK, 0, 2, w, p, NULL);
}

/* refl against PathP L a b is fun _ => a. The line must be constant. */
static const Core *rule_refl(Call *k) {
  Checker *c = k->c;
  const Value *e = k->hint;
  if (e == NULL || e->kind != VAL_PATHP)
    return need_type(k, "PathP L a b");
  if (!conv_values(c->m, c->level + 1u, closure_apply(c->m, e, val_ivar(c->m, c->level)), closure_apply(c->m, e, val_iend(c->m, 0))))
    return nul(FAIL(c, "TYPE_MISMATCH", "refl needs a path type with a constant line, found %s", show(c, e)));
  if (!path_ends(c, e, e->args[0], e->args[0]))
    return NULL;
  k->type = e;
  return core_bind(c, CORE_PLAM, "_", NULL, quote_value(c->m, c->level + 1u, e->args[0]));
}

static const Core *rule_part(Call *k) {
  Checker *c = k->c;
  const Value *pt = NULL;
  const Core *p = infer(c, k->args[0], &pt);
  if (p == NULL)
    return NULL;
  if (!val_is(pt, OP_PROD))
    return nul(FAIL(c, "TYPE_MISMATCH", "%s needs a pair, found a term of type %s", k->b->name, show(c, pt)));
  k->type = pt->args[k->b->part];
  return op3(c, k->b->op, 0, 1, p, NULL, NULL);
}

static const Core *rule_sigma_part(Call *k) {
  Checker *c = k->c;
  const Value *st = NULL;
  const Core *s = infer(c, k->args[0], &st);
  const Core *w;
  if (s == NULL)
    return NULL;
  if (st == NULL || st->kind != VAL_SIGMA)
    return nul(FAIL(c, "TYPE_MISMATCH", "%s needs a Sigma value, found a term of type %s", k->b->name, show(c, st)));
  w = op3(c, OP_WITNESS, 0, 1, s, NULL, NULL);
  k->type = k->b->part == 0u ? st->dom : closure_apply(c->m, st, here(c, w));
  return k->b->part == 0u ? w : op3(c, OP_PAYLOAD, 0, 1, s, NULL, NULL);
}

/* either f g s */
static const Core *rule_either(Call *k) {
  Checker *c = k->c;
  const Value *st = NULL;
  const Value *res = NULL;
  const Core *s = infer(c, k->args[2], &st);
  const Core *f;
  const Core *g;
  if (s == NULL)
    return NULL;
  if (!val_is(st, OP_SUM))
    return nul(FAIL(c, "TYPE_MISMATCH", "either needs a value of type Sum A B, found a term of type %s", show(c, st)));
  f = fn_into(c, k->args[0], st->args[0], k->hint, &res);
  g = f == NULL ? NULL : check(c, k->args[1], val_arrow(c->m, st->args[1], res));
  k->type = res;
  return op3(c, OP_EITHER, 0, 3, f, g, s);
}

/* option z f o */
static const Core *rule_option(Call *k) {
  Checker *c = k->c;
  const Value *ot = NULL;
  const Value *res = k->hint;
  const Core *o = infer(c, k->args[2], &ot);
  const Core *z;
  const Core *f;
  if (o == NULL)
    return NULL;
  if (!val_is(ot, OP_OPTION))
    return nul(FAIL(c, "TYPE_MISMATCH", "option needs a value of type Option A, found a term of type %s", show(c, ot)));
  z = res != NULL ? check(c, k->args[0], res) : infer(c, k->args[0], &res);
  f = z == NULL ? NULL : check(c, k->args[1], val_arrow(c->m, ot->args[0], res));
  k->type = res;
  return op3(c, OP_OPTION_ELIM, 0, 3, z, f, o);
}

/* The type of case I of elim with the motive PV on a value of type ST:
   (a : A) -> P (inl a), (b : B) -> P (inr b), or P unit. S6 u4b1
   (Q-S6-14 (a)): P flagYes, P flagNo; P none, (a : A) -> P (some a);
   (a : A) -> (b : B) -> P (pair a b); P 0, (n : Nat) -> P n ->
   P (natSucc n); P nil, (a : A) -> (l : List A) -> P l -> P (cons a l). */
/* natSucc on an open X as the evaluator gives it (S6 u4b1): a VAL_STUCK
   head, as eval.c nat_succ gives through blocked(). tyop gives a value
   that the Nat ops refuse. */
static const Value *succ_open(Checker *c, const Value *x) {
  const Value *a[1];
  a[0] = x;
  return val_op(c->m, VAL_STUCK, OP_NAT_SUCC, 0, 0, a, 1u);
}

static const Value *elim_case(Checker *c, const Value *pv, const Value *st, uint32_t i) {
  const Value *x = val_var(c->m, c->level);
  const Value *y = val_var(c->m, c->level + 1u);
  if (val_is(st, OP_UNIT))
    return apply_value(c->m, pv, tyop(c, OP_UNIT_VAL, 0, NULL, NULL, NULL));
  if (val_is(st, OP_FLAG))
    return apply_value(c->m, pv, tyop(c, i == 0u ? OP_FLAG_YES : OP_FLAG_NO, 0, NULL, NULL, NULL));
  if (val_is(st, OP_OPTION) && i == 0u)
    return apply_value(c->m, pv, tyop(c, OP_NONE, 0, NULL, NULL, NULL));
  if (val_is(st, OP_OPTION))
    return here(c, core_bind(c, CORE_PI, "a", quote_value(c->m, c->level, st->args[0]),
                             quote_value(c->m, c->level + 1u, apply_value(c->m, pv, tyop(c, OP_SOME, 1, x, NULL, NULL)))));
  if (val_is(st, OP_PROD))
    return here(c, core_bind(c, CORE_PI, "a", quote_value(c->m, c->level, st->args[0]),
                             core_bind(c, CORE_PI, "b", quote_value(c->m, c->level + 1u, st->args[1]),
                                       quote_value(c->m, c->level + 2u, apply_value(c->m, pv, tyop(c, OP_PAIR, 2, x, y, NULL))))));
  if (val_is(st, OP_NAT) && i == 0u)
    return apply_value(c->m, pv, val_nat(c->m, 0));
  if (val_is(st, OP_NAT))
    return here(c, core_bind(c, CORE_PI, "n", quote_value(c->m, c->level, st),
                             core_bind(c, CORE_PI, "ih", quote_value(c->m, c->level + 1u, apply_value(c->m, pv, x)),
                                       quote_value(c->m, c->level + 2u, apply_value(c->m, pv, succ_open(c, x))))));
  if (val_is(st, OP_LIST) && i == 0u)
    return apply_value(c->m, pv, tyop(c, OP_NIL, 0, NULL, NULL, NULL));
  if (val_is(st, OP_LIST))
    return here(c, core_bind(c, CORE_PI, "a", quote_value(c->m, c->level, st->args[0]),
                             core_bind(c, CORE_PI, "l", quote_value(c->m, c->level + 1u, st),
                                       core_bind(c, CORE_PI, "ih", quote_value(c->m, c->level + 2u, apply_value(c->m, pv, y)),
                                                 quote_value(c->m, c->level + 3u, apply_value(c->m, pv, tyop(c, OP_CONS, 2, x, y, NULL)))))));
  return here(c, core_bind(c, CORE_PI, i == 0u ? "a" : "b", quote_value(c->m, c->level, st->args[i]),
                           quote_value(c->m, c->level + 1u, apply_value(c->m, pv, tyop(c, i == 0u ? OP_INL : OP_INR, 1, x, NULL, NULL)))));
}

/* The case count of elim on ST (S6 u4b1, Q-S6-14 (a)): 2 on Sum, Flag,
   Option, Nat and List; 1 on Unit and Prod; 0 when ST has no elim. */
static uint32_t elim_want(const Value *st) {
  static const Op ops[7] = {OP_SUM, OP_FLAG, OP_OPTION, OP_NAT, OP_LIST, OP_UNIT, OP_PROD};
  uint32_t i;
  for (i = 0; i < 7u; i++) {
    if (val_is(st, ops[i]))
      return i < 5u ? 2u : 1u;
  }
  return 0u;
}

/* A printed motive has no binder annotation. Its domain can instead come
   from the scrutinee: at i = 3 for a 2-case elim, at i = 2 for a 1-case
   elim. Try i = 3 first: a 2-case elim can have a Prod case at i = 2. */
static const Value *elim_domain(Checker *c, const Term *const *args, uint32_t argc) {
  const Value *dom = lam_domain(c, args[0]);
  uint32_t i;
  if (dom != NULL || args[0]->kind != TERM_LAM || args[0]->left != NULL)
    return dom;
  /* A domain family outside a block (S7 B1): the scrutinee follows one
     case for each constructor. */
  for (i = 2u; i < argc; i++) {
    if (try_infer(c, args[i], &dom) != NULL && val_is(dom, OP_FAMILY) && c->m->families[dom->inst].block_count == 1u && i == c->m->families[dom->inst].ctor_count + 1u)
      return dom;
  }
  if (argc > 3u && try_infer(c, args[3], &dom) != NULL && elim_want(dom) == 2u)
    return dom;
  if (argc > 2u && try_infer(c, args[2], &dom) != NULL && elim_want(dom) == 1u)
    return dom;
  return NULL;
}

/* The last domain S of the motive type PT = (x1 : X1) -> .. -> (s : S) ->
   Type k, with *D the number of domains before S (S7 B1). */
static const Value *motive_domain(Checker *c, const Value *pt, uint32_t *d) {
  const Value *v = pt;
  uint32_t n;
  for (n = 0; v != NULL && v->kind == VAL_PI; n++) {
    const Value *cod = closure_apply(c->m, v, val_var(c->m, c->level + n));
    if (cod != NULL && cod->kind == VAL_UNIV) {
      *d = n;
      return v->dom;
    }
    v = cod;
  }
  return vnul(FAIL(c, "TYPE_MISMATCH", "elim needs a motive of type X -> Type k, found a term of type %s", show(c, pt)));
}

/* A printed motive over the domain family of ST (S7 B1): one bare binder
   for each index, then one for the value. VALS holds the parameters, then
   the index variables before J. *TYPE gets the core of the motive type. */
static const Core *bare_motive(Checker *c, const Term *t, const Value *st, const Value **vals, uint32_t j, const Core **type) {
  Machine *m = c->m;
  const FamilyInfo *f = &m->families[st->inst];
  uint32_t p = f->param_count;
  uint64_t level = 0;
  const Value *dom;
  const Core *domc;
  const Core *ann = NULL;
  const Core *body;
  const Core *cod = NULL;
  *type = NULL;
  if (t->kind != TERM_LAM)
    return nul(FAIL(c, "TYPE_MISMATCH", "the motive of elim on %s needs one binder for each of its %u indices, then one for the value", f->name, (unsigned)f->index_count));
  dom = j < f->index_count ? eval_core(m, env_of(c, vals, p + j), f->index_types[j]) : val_op(m, VAL_OP, OP_FAMILY, st->inst, 0, vals, p + j);
  if (t->left != NULL && (ann = checked_annotation(c, t->left, dom)) == NULL)
    return NULL;
  domc = quote_value(m, c->level, dom);
  if (domc == NULL || !push(c, t->name, dom))
    return NULL;
  if (j < f->index_count)
    vals[p + j] = val_var(m, c->level - 1u);
  body = j < f->index_count ? bare_motive(c, t->right, st, vals, j + 1u, &cod) : check_type(c, t->right, &level);
  if (body != NULL && j == f->index_count)
    cod = quote_value(m, c->level, val_univ(m, level));
  pop(c);
  *type = cod == NULL ? NULL : core_bind(c, CORE_PI, t->name, domc, cod);
  return body == NULL || *type == NULL ? NULL : core_bind(c, CORE_LAM, t->name, ann, body);
}

static const Core *elim_on_family(Call *k, const Core *motive, const Value *pt, const Value *st, uint32_t d);

/* elim P c1 .. cn x (USER ruling S4): the dependent eliminator of Sum A B
   (two cases) and Unit (one case), with the motive P : X -> Type k and the
   type P x. A domain family outside a block goes to elim_on_family (S7
   B1, O21). S6 u4b1 (Q-S6-13 (b), Q-S6-14 (a)): also Flag, Option A, Nat
   and List A (two cases) and Prod A B (one case); Nat and List get
   dependent induction. A Path has no elim (no K). */
static const Core *rule_elim(Call *k) {
  Checker *c = k->c;
  const Value *st = elim_domain(c, k->args, k->argc);
  const Value *pt = NULL;
  const Value *pv;
  const Core *cores[4] = {NULL, NULL, NULL, NULL};
  const Core *s;
  uint32_t want;
  uint32_t d = 0;
  uint32_t i;
  if (st != NULL && val_is(st, OP_FAMILY) && k->args[0]->kind == TERM_LAM && k->args[0]->left == NULL) {
    const Value **vals = arena_alloc(c->m->arena, ((size_t)st->argc + 1u) * sizeof *vals);
    const Core *ty = NULL;
    for (i = 0; vals != NULL && i < st->argc; i++)
      vals[i] = st->args[i];
    cores[0] = vals == NULL ? nul(FAIL(c, "OOM", "out of memory")) : bare_motive(c, k->args[0], st, vals, 0, &ty);
    pt = here(c, ty);
  } else if (st != NULL && k->args[0]->kind == TERM_LAM && k->args[0]->left == NULL) {
    uint64_t level = 0;
    const Core *body;
    if (!push(c, k->args[0]->name, st))
      return NULL;
    body = check_type(c, k->args[0]->right, &level);
    pop(c);
    cores[0] = core_bind(c, CORE_LAM, k->args[0]->name, NULL, body);
    pt = val_arrow(c->m, st, val_univ(c->m, level));
  } else {
    cores[0] = infer(c, k->args[0], &pt);
  }
  if (cores[0] == NULL)
    return NULL;
  st = motive_domain(c, pt, &d);
  if (st == NULL)
    return NULL;
  if (val_is(st, OP_FAMILY) && c->m->families[st->inst].block_count == 1u)
    return elim_on_family(k, cores[0], pt, st, d);
  want = elim_want(st);
  if (d != 0u || want == 0u)
    return nul(FAIL(c, "TYPE_MISMATCH", "elim needs a motive on Sum A B, Unit, Flag, Option A, Prod A B, Nat, List A or a domain family outside a block, found a motive of type %s", show(c, pt)));
  if (k->argc < want + 2u)
    return nul(FAIL(c, "TYPE_MISMATCH", "elim on %s needs a motive, %u cases and a scrutinee", show(c, st), want));
  s = check(c, k->args[want + 1u], st);
  if (s == NULL)
    return NULL;
  pv = here(c, cores[0]);
  for (i = 0; i < want && cores[i] != NULL; i++)
    cores[i + 1u] = check(c, k->args[i + 1u], elim_case(c, pv, st, i));
  if (cores[want] == NULL)
    return NULL;
  cores[want + 1u] = s;
  k->type = apply_value(c->m, pv, here(c, s));
  k->used = want + 2u;
  return core_op(c, OP_ELIM, want, 0, cores, want + 2u);
}

static const Core *rule_pure(Call *k) {
  Carrier carrier = CARRIER_OPTION;
  const Value *a = NULL;
  if (!carrier_of(k->hint, &carrier, &a))
    return need_type(k, "Option A, List A or Sum E A");
  k->type = k->hint;
  return op3(k->c, OP_PURE, carrier, 1, check(k->c, k->args[0], a), NULL, NULL);
}

/* map f m */
static const Core *rule_map(Call *k) {
  Checker *c = k->c;
  Carrier carrier = CARRIER_OPTION;
  Carrier hint_carrier = CARRIER_OPTION;
  const Value *mt = NULL;
  const Value *a = NULL;
  const Value *b = NULL;
  const Value *hint_elem = NULL;
  const Core *x = carried_arg(k, k->args[1], k->args[0], &mt);
  const Core *f;
  if (x == NULL)
    return NULL;
  if (!carrier_of(mt, &carrier, &a))
    return not_carrier(k, mt);
  f = fn_into(c, k->args[0], a, carrier_of(k->hint, &hint_carrier, &hint_elem) ? hint_elem : NULL, &b);
  k->type = carried(c, mt, b);
  return op3(c, OP_MAP, carrier, 2, f, x, NULL);
}

/* bind m f */
/* A bare lambda `fun y => t`: a TERM_LAM with no binder type. */
static int is_bare_lam(const Term *t) {
  return t != NULL && t->kind == TERM_LAM && t->left == NULL;
}

static const Core *bare_fn_into(Checker *c, const Term *t, const Value *dom, const Value **result);
static const Core *rule_step_let(Call *k);

static const Core *rule_bind(Call *k) {
  Checker *c = k->c;
  Carrier carrier = CARRIER_OPTION;
  Carrier result_carrier = CARRIER_OPTION;
  const Value *mt = NULL;
  const Value *a = NULL;
  const Value *b = NULL;
  const Value *res = NULL;
  const Core *x = carried_arg(k, k->args[0], k->args[1], &mt);
  const Core *f;
  if (x == NULL)
    return NULL;
  if (!carrier_of(mt, &carrier, &a))
    return not_carrier(k, mt);
  /* Q-S5-26 (a): a bare `fun y => t` takes its binder type from the first argument. */
  f = is_bare_lam(k->args[1]) && k->hint == NULL ? bare_fn_into(c, k->args[1], a, &res) : fn_into(c, k->args[1], a, k->hint, &res);
  if (f == NULL)
    return NULL;
  if (!carrier_of(res, &result_carrier, &b) || result_carrier != carrier)
    return nul(FAIL(c, "TYPE_MISMATCH", "bind needs a function into the carrier of %s, found one into %s", show(c, mt), show(c, res)));
  if (carrier == CARRIER_SUM && !conv_values(c->m, c->level, mt->args[0], res->args[0]))
    return nul(FAIL(c, "TYPE_MISMATCH", "bind must preserve the Sum error type %s, found %s", show(c, mt->args[0]), show(c, res->args[0])));
  k->type = res;
  return op3(c, OP_BIND, carrier, 2, x, f, NULL);
}

/* filter p m */
static const Core *rule_filter(Call *k) {
  Checker *c = k->c;
  Carrier carrier = CARRIER_OPTION;
  const Value *mt = NULL;
  const Value *a = NULL;
  const Core *x = carried_arg(k, k->args[1], k->args[0], &mt);
  const Core *p;
  if (x == NULL)
    return NULL;
  if (!carrier_of(mt, &carrier, &a) || carrier == CARRIER_SUM)
    return nul(FAIL(c, "TYPE_MISMATCH", "filter needs a value of type Option A or List A, found a term of type %s", show(c, mt)));
  p = check(c, k->args[0], val_arrow(c->m, a, flag_type(c)));
  k->type = mt;
  return op3(c, OP_FILTER, carrier, 2, p, x, NULL);
}

/* fold step z n (Nat) or fold f z xs (List A). */
static const Core *fold_simple(Call *k, const Core *s, const Value *st) {
  Checker *c = k->c;
  const Value *res = k->hint;
  const Core *z = res != NULL ? check(c, k->args[1], res) : infer(c, k->args[1], &res);
  int list = val_is(st, OP_LIST);
  const Value *step = list ? val_arrow(c->m, st->args[0], val_arrow(c->m, res, res)) : val_arrow(c->m, res, res);
  const Core *f = z == NULL ? NULL : check(c, k->args[0], step);
  k->used = 3u;
  k->type = res;
  return op3(c, list ? OP_FOLD_LIST : OP_FOLD_NAT, 0, 3, f, z, s);
}

/* The Pi telescope of the fold case of CTOR around BODY, a core at the
   level c->level + field_count: one argument for each field (a recursive
   field arrives folded, so its type is RES). Field k is the variable at
   level c->level + k, its type at the parameters ENV and the earlier
   fields (S4 item 13). A path field `Path F x y` arrives folded, so its
   type is `Path RES x' y'` (S4 item 14). */
/* The folded type of a recursive field of type T: the target of its sort
   in a block fold (S6), else RES. */
static const Value *sort_res(const Checker *c, const Core *t, const Value *res) {
  return c->fold_targets != NULL && t != NULL && t->kind == CORE_OP && t->op == OP_FAMILY && t->inst >= c->fold_first && t->inst - c->fold_first < c->fold_count ? c->fold_targets[t->inst - c->fold_first] : res;
}

/* The binder position of the field I in a case. An elim case (S7 B1) has
   the IH of each recursive or path field after the field. */
static uint32_t field_pos(const Checker *c, const CtorInfo *ctor, uint32_t i) {
  uint32_t pos = i;
  uint32_t j;
  for (j = 0; j < i && c->elim_motive != NULL; j++)
    pos += ctor->fields[j].recursive || ctor->fields[j].path ? 1u : 0u;
  return pos;
}

/* The motive PV at the indices of the family type T, then at X (S7 B1). */
static const Value *motive_at(Checker *c, const Value *pv, const Value *t, const Value *x) {
  const Value *acc = pv;
  uint32_t i;
  if (t == NULL || x == NULL || pv == NULL)
    return NULL;
  if (!val_is(t, OP_FAMILY))
    return vnul(FAIL(c, "TYPE_MISMATCH", "an elim case needs a value of a domain family here"));
  for (i = c->m->families[t->inst].param_count; i < t->argc && acc != NULL; i++)
    acc = apply_value(c->m, acc, t->args[i]);
  return acc == NULL ? NULL : apply_value(c->m, acc, x);
}

/* The IH of the end E of a path field in an elim case: the variable after
   E (S7 B1). */
static const Value *ih_end(Checker *c, const Value *e) {
  return e != NULL && e->kind == VAL_VAR && e->nat >= c->level ? val_var(c->m, e->nat + 1u) : NULL;
}

/* The IH type of the recursive or path field FIELD of CTOR at the level AT,
   a core at AT + 1 (S7 B1): P idx x for a recursive field x, and PathP (fun
   i => P idx (x @ i)) ih0 ih1 for a path field, with ih0 and ih1 the IHs of
   its ends. ENV holds the parameters and the earlier fields. */
static const Core *ih_type(Checker *c, const CtorInfo *ctor, const FieldInfo *field, const Env *env, uint32_t at) {
  Machine *m = c->m;
  const Value *x = val_var(m, at);
  const Value *r = val_ivar(m, at + 1u);
  const Env *inner = env_push(m, env, r);
  uint32_t e0 = c->level + field_pos(c, ctor, field->ends[0]);
  uint32_t e1 = c->level + field_pos(c, ctor, field->ends[1]);
  const Value *line;
  if (!field->path)
    return quote_value(m, at + 1u, motive_at(c, c->elim_motive, eval_core(m, env, field->type), x));
  line = inner == NULL ? NULL : motive_at(c, c->elim_motive, eval_core(m, inner, field->type->b), path_apply(m, x, r, val_var(m, e0), val_var(m, e1)));
  return line == NULL ? NULL : core_ends(c, CORE_PATHP, "_", NULL, quote_value(m, at + 2u, line), quote_value(m, at + 1u, val_var(m, e0 + 1u)), quote_value(m, at + 1u, val_var(m, e1 + 1u)));
}

/* The motive at the constructor INST at the parameters of ST, the field
   variables at their elim case positions and the interval values R0 and
   R1, at the result indices of INST (S7 B1). */
static const Value *elim_res(Checker *c, uint32_t inst, const Value *st, const Value *r0, const Value *r1) {
  Machine *m = c->m;
  const CtorInfo *ctor = &m->ctors[inst];
  const FamilyInfo *f = &m->families[ctor->family];
  uint32_t p = f->param_count;
  uint32_t n = ctor->field_count;
  uint32_t d = ctor->interval_count;
  uint32_t q = ctor->result == NULL ? p : p + f->index_count;
  const Value **a = arena_alloc(m->arena, ((size_t)p + n + d + 1u) * sizeof *a);
  const Value **t = arena_alloc(m->arena, ((size_t)q + 1u) * sizeof *t);
  const Env *env = env_of(c, st->args, p);
  uint32_t i;
  int ok = 1;
  if (a == NULL || t == NULL)
    return vnul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < p; i++) {
    a[i] = st->args[i];
    t[i] = st->args[i];
  }
  /* An empty ENV is NULL (a family without parameters), so only a failed
     push stops the loops. */
  for (i = 0; i < n && ok; i++) {
    a[p + i] = val_var(m, c->level + field_pos(c, ctor, i));
    env = env_push(m, env, a[p + i]);
    ok = env != NULL;
  }
  for (i = p; i < q && ok; i++) {
    t[i] = eval_core(m, env, ctor->result[i - p]);
    ok = t[i] != NULL;
  }
  if (!ok)
    return NULL;
  if (d > 0u)
    a[p + n] = r0;
  if (d > 1u)
    a[p + n + 1u] = r1;
  return motive_at(c, c->elim_motive, val_op(m, VAL_OP, OP_FAMILY, ctor->family, 0, t, q), val_ctor(m, inst, a, p + n + d));
}

/* The line of a path case at R0 and R1: RES in a fold, the motive at the
   constructor in an elim (S7 B1). */
static const Value *line_res(Checker *c, uint32_t inst, const Value *st, const Value *res, const Value *r0, const Value *r1) {
  return c->elim_motive == NULL ? res : elim_res(c, inst, st, r0, r1);
}

static const Core *case_fields(Checker *c, const CtorInfo *ctor, const Env *env, const Value *res, const Core *body) {
  Machine *m = c->m;
  uint32_t n = ctor->field_count;
  const Core **types = arena_alloc(m->arena, ((size_t)n + 1u) * sizeof *types);
  const Core **ihs = arena_alloc(m->arena, ((size_t)n + 1u) * sizeof *ihs);
  const Core *t = body;
  uint32_t i;
  if (body == NULL)
    return NULL;
  if (types == NULL || ihs == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < n; i++) {
    const FieldInfo *field = &ctor->fields[i];
    uint32_t at = c->level + field_pos(c, ctor, i);
    int ih = c->elim_motive != NULL && (field->recursive || field->path);
    /* A recursive field at an index over an earlier recursive field (S6)
       arrives folded: the fold is not dependent, so the index goes. An
       elim case (S7 B1) keeps the field. */
    if (c->elim_motive == NULL && field->over_recursive && !field->path && !field->recursive)
      return nul(FAIL(c, "HIT_BOUNDARY", "the fold of %s has no case type for the field %s: a field over an earlier recursive field must be Path F x y, with x and y earlier recursive fields", ctor->name, field->name));
    if (c->elim_motive != NULL)
      types[i] = quote_value(m, at, eval_core(m, env, field->type));
    else
      types[i] = field->path ? core_ends(c, CORE_PATHP, "_", NULL, quote_value(m, at + 1u, sort_res(c, field->type->b, res)), quote_value(m, at, val_var(m, c->level + field->ends[0])), quote_value(m, at, val_var(m, c->level + field->ends[1]))) : quote_value(m, at, field->recursive ? sort_res(c, field->type, res) : eval_core(m, env, field->type));
    ihs[i] = ih ? ih_type(c, ctor, field, env, at) : NULL;
    env = env_push(m, env, val_var(m, at));
    if (types[i] == NULL || env == NULL || (ih && ihs[i] == NULL))
      return NULL;
  }
  for (i = n; i > 0u && t != NULL; i--) {
    t = ihs[i - 1u] == NULL ? t : core_bind(c, CORE_PI, "ih", ihs[i - 1u], t);
    t = t == NULL ? NULL : core_bind(c, CORE_PI, ctor->fields[i - 1u].name, types[i - 1u], t);
  }
  return t;
}

/* The type of the fold case of CTOR: the fields, then RES. */
static const Value *case_type(Checker *c, const CtorInfo *ctor, const Env *env, const Value *res) {
  return here(c, case_fields(c, ctor, env, res, quote_value(c->m, c->level + ctor->field_count, res)));
}

/* The fold image of V, a boundary value of a path constructor of FAM at the
   field variables (S4 R4 (a)). A field variable (a level from c->level up)
   is its folded variable; a point constructor is its case, one of the DONE
   cases in CORES, at the images of its fields. Path fields are mapped
   under a fresh interval binder. ENV and LEVEL include the boundary
   fields and surrounding interval binders to preserve captures. */
static const Value *fold_image(Checker *c, uint32_t fam, const Core *const *cores, uint32_t done, const Value *v, const Env *env, uint32_t level) {
  Machine *m = c->m;
  const FamilyInfo *f = &m->families[fam];
  /* The constructor slots of a block are contiguous (S6). */
  uint32_t base = m->families[f->block_first].first_ctor;
  const CtorInfo *ci;
  const Value *acc;
  uint32_t i;
  if (v == NULL)
    return NULL;
  /* In an elim case (S7 B1) the IH of the field at L is at L + 1. */
  if (v->kind == VAL_VAR && v->nat >= c->level)
    return c->elim_motive == NULL ? v : val_var(m, v->nat + 1u);
  /* p @ r for a path field p (dimension 2, S4 item 15): the folded p has
     the same level, and its ends are earlier recursive fields. In an elim
     case it is the IH path at r. */
  if (v->kind == VAL_PAPP && v->dom != NULL && v->dom->kind == VAL_VAR && v->dom->nat >= c->level)
    return c->elim_motive == NULL ? v : path_apply(m, val_var(m, v->dom->nat + 1u), v->arg, ih_end(c, v->argc == 2u ? v->args[0] : NULL), ih_end(c, v->argc == 2u ? v->args[1] : NULL));
  if (!val_is(v, OP_CTOR) || v->inst < base || v->inst - base >= done || m->ctors[v->inst].interval_count != 0u)
    return vnul(FAIL(c, "HIT_BOUNDARY", "the fold cannot map the boundary term %s: a boundary term must be a field, a path field at an interval, or an earlier point constructor", show(c, v)));
  ci = &m->ctors[v->inst];
  acc = here(c, cores[v->inst - base]);
  for (i = 0; i < ci->field_count && acc != NULL; i++) {
    const FieldInfo *field = &ci->fields[i];
    const Value *arg = v->args[f->param_count + i];
    /* An elim case takes the field, then its IH (S7 B1). */
    if (c->elim_motive != NULL && (field->recursive || field->path))
      acc = apply_value(m, acc, arg);
    if (field->recursive)
      arg = fold_image(c, fam, cores, done, arg, env, level);
    else if (field->path) {
      const Value *r = val_ivar(m, level);
      const Env *inner = env_push(m, env, r);
      const Value *at = inner == NULL ? NULL : path_apply(m, arg, r, v->args[f->param_count + field->ends[0]], v->args[f->param_count + field->ends[1]]);
      const Value *image = at == NULL ? NULL : fold_image(c, fam, cores, done, at, inner, level + 1u);
      arg = image == NULL ? NULL : val_closure(m, VAL_PLAM, "_", NULL, env, quote_value(m, level + 1u, image));
    }
    acc = arg == NULL || acc == NULL ? NULL : apply_value(m, acc, arg);
  }
  return acc;
}

/* The fold image of the constructor INST at the parameters of ST, the
   field variables (field k at level c->level + k) and the interval values
   R0 (and R1 at dimension 2). At an end it is the image of the boundary. */
static const Value *case_image(Checker *c, uint32_t inst, const Value *st, const Core *const *cores, uint32_t done, const Value *r0, const Value *r1, uint32_t level) {
  Machine *m = c->m;
  const CtorInfo *ctor = &m->ctors[inst];
  uint32_t p = m->families[ctor->family].param_count;
  uint32_t n = ctor->field_count;
  uint32_t d = ctor->interval_count;
  uint32_t b = field_pos(c, ctor, n);
  const Value **a = arena_alloc(m->arena, ((size_t)p + n + d) * sizeof *a);
  const Env *env = c->env;
  uint32_t i;
  if (a == NULL)
    return vnul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < p; i++)
    a[i] = st->args[i];
  /* An elim case (S7 B1) has the IH binders between the fields. */
  for (i = 0; i < n; i++)
    a[p + i] = val_var(m, c->level + field_pos(c, ctor, i));
  for (i = 0; i < b; i++) {
    env = env_push(m, env, val_var(m, c->level + i));
    if (env == NULL)
      return NULL;
  }
  for (i = c->level + b; i < level; i++) {
    env = env_push(m, env, val_ivar(m, i));
    if (env == NULL)
      return NULL;
  }
  a[p + n] = r0;
  if (d == 2u)
    a[p + n + 1u] = r1;
  return fold_image(c, ctor->family, cores, done, val_ctor(m, inst, a, p + n + d), env, level);
}

/* The square type of the fold case of INST at dimension 2 (S4 item 15), a
   core at L = c->level + field_count:
   PathP (fun (i : I) => PathP (fun (_ : I) => RES) X(i) Y(i)) P Q,
   with X(i) and Y(i) the images at (i, i0) and (i, i1), and P and Q the
   paths fun (j : I) => the image at (i0, j) and (i1, j). For squash0 it is
   Path (Path RES x' y') p' q' (with path eta, R11), so the case type is
   isSet RES (R8 (a)). */
static const Core *square_type(Checker *c, uint32_t inst, const Value *st, const Value *res, const Core *const *cores, uint32_t done) {
  Machine *m = c->m;
  uint32_t l = c->level + field_pos(c, &m->ctors[inst], m->ctors[inst].field_count);
  const Value *i = val_ivar(m, l);
  const Core *x = quote_value(m, l + 1u, case_image(c, inst, st, cores, done, i, val_iend(m, 0), l + 1u));
  const Core *y = x == NULL ? NULL : quote_value(m, l + 1u, case_image(c, inst, st, cores, done, i, val_iend(m, 1), l + 1u));
  const Core *inner = y == NULL ? NULL : core_ends(c, CORE_PATHP, "_", NULL, quote_value(m, l + 2u, line_res(c, inst, st, res, i, val_ivar(m, l + 1u))), x, y);
  const Core *ends[2];
  int side;
  for (side = 0; side < 2; side++) {
    ends[side] = inner == NULL ? NULL : core_bind(c, CORE_PLAM, "_", NULL, quote_value(m, l + 1u, case_image(c, inst, st, cores, done, val_iend(m, side), i, l + 1u)));
    if (ends[side] == NULL)
      return NULL;
  }
  return core_ends(c, CORE_PATHP, "_", NULL, inner, ends[0], ends[1]);
}

/* The type of the fold case of the path constructor INST: (folded fields)
   -> PathP (fun (_ : I) => RES) B0 B1 at dimension 1, with B0 and B1 the
   fold images of the boundary at i0 and i1, or the square type at
   dimension 2. Field k is the variable at level c->level + k: the field in
   the boundary, its folded value in the image. */
static const Value *path_case_type(Checker *c, uint32_t inst, const Value *st, const Value *res, const Core *const *cores, uint32_t done) {
  Machine *m = c->m;
  const CtorInfo *ctor = &m->ctors[inst];
  const Env *env = env_of(c, st->args, m->families[ctor->family].param_count);
  uint32_t l = c->level + field_pos(c, ctor, ctor->field_count);
  const Core *ends[2];
  const Core *t;
  int side;
  if (ctor->interval_count != 1u && ctor->interval_count != 2u)
    return vnul(FAIL(c, "HIT_BOUNDARY", "a fold of %s, a constructor with %u interval fields, is not in S4: S4 folds dimensions 1 and 2", ctor->name, (unsigned)ctor->interval_count));
  if (ctor->interval_count == 2u)
    return here(c, case_fields(c, ctor, env, res, square_type(c, inst, st, res, cores, done)));
  for (side = 0; side < 2; side++)
    ends[side] = quote_value(m, l, case_image(c, inst, st, cores, done, val_iend(m, side), NULL, l));
  t = ends[0] == NULL || ends[1] == NULL ? NULL : core_ends(c, CORE_PATHP, "_", NULL, quote_value(m, l + 1u, line_res(c, inst, st, res, val_ivar(m, l), NULL)), ends[0], ends[1]);
  return here(c, case_fields(c, ctor, env, res, t));
}

/* fold case... x over a domain family: one case for each constructor. */
static const Core *fold_family(Call *k, const Core *s, const Value *st) {
  Checker *c = k->c;
  Machine *m = c->m;
  const FamilyInfo *f = &m->families[st->inst];
  const Env *env = env_of(c, st->args, f->param_count);
  const Value *res = k->hint;
  const Core **cores = arena_alloc(m->arena, ((size_t)f->ctor_count + 2u) * sizeof *cores);
  uint32_t j;
  if (cores == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  const Value *ct;
  if (res == NULL && m->ctors[f->first_ctor].field_count == 0u && m->ctors[f->first_ctor].interval_count == 0u)
    cores[0] = infer(c, k->args[0], &res);
  if (res == NULL)
    return nul(FAIL(c, "TYPE_INFER", "fold over %s needs a declared result type here", f->name));
  for (j = 0; j < f->ctor_count; j++) {
    ct = cores[j] != NULL ? NULL : m->ctors[f->first_ctor + j].interval_count == 0u ? case_type(c, &m->ctors[f->first_ctor + j], env, res) : path_case_type(c, f->first_ctor + j, st, res, cores, j);
    cores[j] = cores[j] != NULL ? cores[j] : ct == NULL ? NULL : check(c, k->args[j], ct);
    if (cores[j] == NULL)
      return NULL;
  }
  /* The result type RES goes before the scrutinee: the fold of a formal
     hcomp is an hcomp in RES (S4 R3 (a)). */
  cores[f->ctor_count] = quote_value(m, c->level, res);
  cores[f->ctor_count + 1u] = s;
  if (cores[f->ctor_count] == NULL)
    return NULL;
  k->used = f->ctor_count + 1u;
  k->type = res;
  return core_op(c, OP_FOLD_FAMILY, st->inst, 0, cores, f->ctor_count + 2u);
}

static uint32_t find_family(const Machine *m, const char *name);

/* FAM is the family Bag or Pfin of domain/domain.lang (S2 and S3, USER
   ruling Q-S2-4 (a)). A fold or elim out of Bag or Pfin with a wrong
   count of cases gives REFUSE_BAG_NONCOMM: the comm case is the
   commutative clause (law L1) and, at Pfin, the pfinIdem case is the
   idempotent clause (law L2). At Trace (S6 u3), the traceSwap case is
   the swap clause of the ind pairs. Other families keep TYPE_MISMATCH. */
static int bag_family(const Machine *m, uint32_t fam) {
  return fam != NO_FAMILY && (fam == find_family(m, "Bag") || fam == find_family(m, "Pfin") || fam == find_family(m, "Trace"));
}

/* The clause text of REFUSE_BAG_NONCOMM at FAM (S3): Pfin adds the idem
   case (law L2). */
static const char *bag_clause(const Machine *m, uint32_t fam) {
  return fam == find_family(m, "Pfin") ? "the pfinComm case is the commutative clause (law L1) and the pfinIdem case is the idempotent clause (law L2)" : fam == find_family(m, "Trace") ? "the traceSwap case is the swap clause of the ind pairs (S6 u3)" : "the bagComm case is the commutative clause (law L1)";
}

/* elim P c1 .. cn x over the domain family of ST outside a block (S7 B1,
   O21): the motive type PT is (idx) -> F params idx -> Type k, with D the
   index count. Each case takes the fields, with the IH of a recursive or
   path field after it. The type is P idx' x. The motive goes in
   c->elim_motive only while a case type is built, not while a case is
   checked, so a fold or elim in a case is not in elim mode. */
static const Core *elim_on_family(Call *k, const Core *motive, const Value *pt, const Value *st, uint32_t d) {
  Checker *c = k->c;
  Machine *m = c->m;
  const FamilyInfo *f = &m->families[st->inst];
  uint32_t p = f->param_count;
  uint32_t want = f->ctor_count;
  const Core **cores = arena_alloc(m->arena, ((size_t)want + 2u) * sizeof *cores);
  const Value *xt = NULL;
  const Value *v = pt;
  const Value *pv;
  const Env *env;
  const Core *s;
  uint32_t j;
  int ok;
  if (cores == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  if (f->index_count != d)
    return nul(FAIL(c, "TYPE_MISMATCH", "elim on %s needs a motive over its %u indices, then a value, found a motive of type %s", f->name, (unsigned)f->index_count, show(c, pt)));
  if (k->argc < want + 2u && bag_family(m, st->inst))
    return nul(FAIL(c, "REFUSE_BAG_NONCOMM", "elim on %s needs a motive, %u cases and a scrutinee: %s", f->name, (unsigned)want, bag_clause(m, st->inst)));
  if (k->argc < want + 2u)
    return nul(FAIL(c, "TYPE_MISMATCH", "elim on %s needs a motive, %u cases and a scrutinee", f->name, (unsigned)want));
  s = infer(c, k->args[want + 1u], &xt);
  if (s == NULL)
    return NULL;
  if (!val_is(xt, OP_FAMILY) || xt->inst != st->inst)
    return nul(FAIL(c, "TYPE_MISMATCH", "elim with a motive on %s needs a scrutinee of %s, found a term of type %s", f->name, f->name, show(c, xt)));
  /* The parameters of the motive domain are the scrutinee parameters; the
     motive takes the index types, then the family at its own indices. */
  env = env_of(c, xt->args, p);
  for (j = 0; j < p; j++) {
    if (!conv_values(m, c->level + d, st->args[j], xt->args[j]))
      return nul(FAIL(c, "TYPE_MISMATCH", "the motive of elim has the type %s, but the scrutinee has the type %s", show(c, pt), show(c, xt)));
  }
  for (j = 0; j < d && v != NULL; j++) {
    const Value *it = eval_core(m, env, f->index_types[j]);
    if (it == NULL || v->kind != VAL_PI || !conv_values(m, c->level + j, v->dom, it))
      return nul(FAIL(c, "TYPE_MISMATCH", "the motive of elim on %s must take its indices, then a value, found a motive of type %s", f->name, show(c, pt)));
    env = env_push(m, env, val_var(m, c->level + j));
    v = env == NULL ? NULL : closure_apply(m, v, val_var(m, c->level + j));
  }
  for (j = 0; j < d && v != NULL; j++) {
    if (!conv_values(m, c->level + d, st->args[p + j], val_var(m, c->level + j)))
      return nul(FAIL(c, "TYPE_MISMATCH", "the motive of elim on %s must take its indices, then a value at those indices, found a motive of type %s", f->name, show(c, pt)));
  }
  pv = v == NULL ? NULL : here(c, motive);
  cores[0] = motive;
  for (j = 0, ok = pv != NULL; ok && j < want; j++) {
    uint32_t inst = f->first_ctor + j;
    const CtorInfo *ctor = &m->ctors[inst];
    const Value *ct;
    c->elim_motive = pv;
    ct = ctor->interval_count != 0u ? path_case_type(c, inst, xt, NULL, cores + 1, j) : here(c, case_fields(c, ctor, env_of(c, xt->args, p), NULL, quote_value(m, c->level + field_pos(c, ctor, ctor->field_count), elim_res(c, inst, xt, NULL, NULL))));
    c->elim_motive = NULL;
    cores[j + 1u] = ct == NULL ? NULL : check(c, k->args[j + 1u], ct);
    ok = cores[j + 1u] != NULL;
  }
  if (!ok)
    return NULL;
  cores[want + 1u] = s;
  k->type = motive_at(c, pv, xt, here(c, s));
  k->used = want + 2u;
  return k->type == NULL ? NULL : core_op(c, OP_ELIM, want, st->inst + 1u, cores, want + 2u);
}

/* The case of the constructor slot J of the block fold of ST into the
   TARGETS of the sorts from FIRST (S6). The constructor slots start at
   BASE; CORES holds the TOTAL cases. */
static int block_case(Call *k, const Value *st, const Value *const *targets, uint32_t first, uint32_t base, const Core **cores, uint32_t total, uint32_t j) {
  Checker *c = k->c;
  Machine *m = c->m;
  const CtorInfo *ctor = &m->ctors[base + j];
  const Value *res = targets[ctor->family - first];
  const Value *ct;
  c->fold_targets = targets;
  c->fold_first = first;
  c->fold_count = m->families[first].block_count;
  ct = ctor->interval_count == 0u ? case_type(c, ctor, env_of(c, st->args, m->families[first].param_count), res) : path_case_type(c, base + j, st, res, cores, total);
  c->fold_targets = NULL;
  cores[j] = ct == NULL ? NULL : check(c, k->args[c->fold_count + j], ct);
  return cores[j] != NULL;
}

/* fold T1 .. Tn case... x over a block of n sorts (S6): one target type
   for each sort, then one case for each constructor of each sort in slot
   order, then x. A recursive field of a sort arrives folded at the target
   of that sort. The point cases are checked first, so a boundary can name
   a point constructor of a later sort. The core holds the cases, the n
   targets, the target of x and x. */
static const Core *fold_block(Call *k, const Core *s, const Value *st) {
  Checker *c = k->c;
  Machine *m = c->m;
  const FamilyInfo *f = &m->families[st->inst];
  uint32_t first = f->block_first;
  uint32_t n = f->block_count;
  const FamilyInfo *last = &m->families[first + n - 1u];
  uint32_t base = m->families[first].first_ctor;
  uint32_t total = last->first_ctor + last->ctor_count - base;
  const Value **targets = arena_alloc(m->arena, (size_t)n * sizeof *targets);
  const Core **cores = arena_alloc(m->arena, ((size_t)total + n + 2u) * sizeof *cores);
  uint32_t j;
  int pass;
  if (targets == NULL || cores == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  if (k->argc != n + total + 1u)
    return nul(FAIL(c, "TYPE_MISMATCH", "fold over the block of %s needs %u target types, one case for each of its %u constructors, and the value; found %u arguments", f->name, (unsigned)n, (unsigned)total, (unsigned)k->argc));
  /* Every case is instantiated with the scrutinee's parameters. Check
     that those parameters inhabit the telescope of every block sort. */
  for (j = 0; j < n; j++) {
    const FamilyInfo *sort = &m->families[first + j];
    uint32_t p;
    if (sort->param_count != f->param_count)
      return nul(FAIL(c, "TYPE_MISMATCH", "fold over the block of %s needs the same parameter telescope for every sort", f->name));
    for (p = 0; p < f->param_count; p++) {
      const Env *env = env_of(c, st->args, p);
      if (!expect(c, eval_core(m, env, f->param_types[p]), eval_core(m, env, sort->param_types[p])))
        return NULL;
    }
  }
  memset(cores, 0, ((size_t)total + n + 2u) * sizeof *cores);
  for (j = 0; j < n; j++) {
    uint64_t level = 0;
    cores[total + j] = check_type(c, k->args[j], &level);
    targets[j] = cores[total + j] == NULL ? NULL : here(c, cores[total + j]);
    if (targets[j] == NULL)
      return NULL;
  }
  for (pass = 0; pass < 2; pass++)
    for (j = 0; j < total; j++)
      if ((m->ctors[base + j].interval_count != 0u) == (pass == 1) && !block_case(k, st, targets, first, base, cores, total, j))
        return NULL;
  cores[total + n] = cores[total + (st->inst - first)];
  cores[total + n + 1u] = s;
  k->used = n + total + 1u;
  k->type = targets[st->inst - first];
  return core_op(c, OP_FOLD_FAMILY, st->inst, 0, cores, total + n + 2u);
}

static int simple_scrutinee(const Value *t) {
  return val_is(t, OP_NAT) || val_is(t, OP_LIST);
}

/* FAM is a sort of the block whose fields are checked (S6). */
static int in_block(const Checker *c, uint32_t fam) {
  return c->self != NO_FAMILY && fam >= c->self && fam - c->self < c->self_count;
}

/* fold takes its scrutinee last, so the scrutinee type sets the arity. */
static const Core *rule_fold(Call *k) {
  Checker *c = k->c;
  const Value *st = NULL;
  const Core *s = try_infer(c, k->args[k->argc - 1u], &st);
  uint32_t fam = val_is(st, OP_FAMILY) ? st->inst : NO_FAMILY;
  if (s != NULL && fam != NO_FAMILY) {
    /* The constructor slots of a block are reserved before its
       constructors are checked (S6), so the test is the block. */
    if (in_block(c, fam))
      return nul(FAIL(c, "HIT_BOUNDARY", "a constructor boundary cannot fold %s before all of its constructors are checked", c->m->families[fam].name));
    if (c->m->families[fam].block_count > 1u) {
      k->hint = k->outer;
      return fold_block(k, s, st);
    }
  }
  if (s != NULL && fam != NO_FAMILY && c->m->families[fam].ctor_count + 1u == k->argc) {
    k->hint = k->outer;
    return fold_family(k, s, st);
  }
  /* REFUSE_BAG_NONCOMM (S2 and S3, USER ruling Q-S2-4 (a)): a fold out
     of Bag or Pfin with a wrong count of cases. */
  if (s != NULL && bag_family(c->m, fam))
    return nul(FAIL(c, "REFUSE_BAG_NONCOMM", "a fold out of %s needs %u cases, one for each constructor, and found %u: %s", c->m->families[fam].name, (unsigned)c->m->families[fam].ctor_count, (unsigned)(k->argc - 1u), bag_clause(c->m, fam)));
  if (s != NULL && k->argc == 3u && simple_scrutinee(st)) {
    k->hint = k->outer;
    return fold_simple(k, s, st);
  }
  s = k->argc > 3u ? try_infer(c, k->args[2], &st) : NULL;
  if (s != NULL && simple_scrutinee(st)) {
    k->hint = NULL;
    return fold_simple(k, s, st);
  }
  s = infer(c, k->args[k->argc - 1u], &st);
  return s == NULL ? NULL : nul(FAIL(c, "TYPE_MISMATCH", "fold needs a last argument of type Nat, List A or a domain family, and one case for each constructor; found %u arguments and a last argument of type %s", k->argc, show(c, st)));
}

/* unfold g limit seed, with g : S -> Option (Prod A S). */
static const Core *rule_unfold(Call *k) {
  Checker *c = k->c;
  const Value *st = NULL;
  const Value *a;
  const Core *seed;
  const Core *limit;
  const Core *g;
  if (!val_is(k->hint, OP_LIST))
    return need_type(k, "List A");
  a = k->hint->args[0];
  seed = infer(c, k->args[2], &st);
  limit = seed == NULL ? NULL : check(c, k->args[1], nat_type(c));
  g = limit == NULL ? NULL : check(c, k->args[0], val_arrow(c->m, st, tyop(c, OP_OPTION, 1, tyop(c, OP_PROD, 2, a, st, NULL), NULL, NULL)));
  k->type = k->hint;
  return op3(c, OP_UNFOLD, 0, 3, g, limit, seed);
}

/* The binder name of a path abstraction made from a path type: the name of
   its line, or `i` for the constant line `_` of Path. The printed term must
   name the variable that its body uses. */
static const char *path_binder(const char *name) {
  return name == NULL || strcmp(name, "_") == 0 ? "i" : name;
}

/* sym p is (fun q => fun i => q @ ~i) p, of type PathP (fun i => L[~i]) b a
   for p : PathP L a b. The application keeps p outside the interval
   binder, so p needs no shift. */
static const Core *rule_sym(Call *k) {
  Checker *c = k->c;
  const Value *pt = NULL;
  const Core *p = infer_path(k, 0, &pt);
  const Core *flip;
  const Core *line;
  const Core *body;
  if (p == NULL)
    return NULL;
  flip = core_iop(c, CORE_INEG, core_index(c, CORE_VAR, 0), NULL);
  line = quote_value(c->m, c->level + 1u, closure_apply(c->m, pt, at(c, flip, val_ivar(c->m, c->level))));
  k->type = here(c, core_ends(c, CORE_PATHP, pt->name, NULL, line, quote_value(c->m, c->level, pt->args[1]), quote_value(c->m, c->level, pt->args[0])));
  body = core_ends(c, CORE_PAPP, NULL, core_index(c, CORE_VAR, 1), flip, quote_value(c->m, c->level + 2u, pt->args[0]), quote_value(c->m, c->level + 2u, pt->args[1]));
  return core_app(c, core_bind(c, CORE_LAM, "q", NULL, core_bind(c, CORE_PLAM, path_binder(pt->name), NULL, body)), p);
}

/* cong f p is (fun g => fun q => fun i => g (q @ i)) f p, for
   f : (x : A) -> B and p : Path A a b, of type
   PathP (fun i => B[p @ i]) (f a) (f b). */
static const Core *rule_cong(Call *k) {
  Checker *c = k->c;
  const Value *pt = NULL;
  const Value *ft = NULL;
  const Value *i = val_ivar(c->m, c->level);
  const Core *p = infer_path(k, 1, &pt);
  const Core *f = p == NULL ? NULL : try_infer(c, k->args[0], &ft);
  const Value *fv;
  const Value *pv;
  const Core *line;
  const Core *body;
  if (p == NULL)
    return NULL;
  if (f == NULL) {
    ft = k->hint != NULL && k->hint->kind == VAL_PATHP ? val_arrow(c->m, closure_apply(c->m, pt, val_iend(c->m, 0)), closure_apply(c->m, k->hint, val_iend(c->m, 0))) : NULL;
    f = ft != NULL ? check(c, k->args[0], ft) : infer(c, k->args[0], &ft);
  }
  if (f == NULL)
    return NULL;
  if (ft == NULL || ft->kind != VAL_PI)
    return nul(FAIL(c, "TYPE_NOT_FUNCTION", "cong needs a function, found a term of type %s", show(c, ft)));
  if (!conv_values(c->m, c->level + 1u, closure_apply(c->m, pt, i), ft->dom))
    return nul(FAIL(c, "TYPE_MISMATCH", "cong needs a path in %s, found a term of type %s", show(c, ft->dom), show(c, pt)));
  fv = here(c, f);
  pv = here(c, p);
  line = quote_value(c->m, c->level + 1u, closure_apply(c->m, ft, path_apply(c->m, pv, i, pt->args[0], pt->args[1])));
  k->type = here(c, core_ends(c, CORE_PATHP, pt->name, NULL, line, quote_value(c->m, c->level, apply_value(c->m, fv, pt->args[0])), quote_value(c->m, c->level, apply_value(c->m, fv, pt->args[1]))));
  body = core_app(c, core_index(c, CORE_VAR, 2), core_ends(c, CORE_PAPP, NULL, core_index(c, CORE_VAR, 1), core_index(c, CORE_VAR, 0), quote_value(c->m, c->level + 3u, pt->args[0]), quote_value(c->m, c->level + 3u, pt->args[1])));
  return core_app(c, core_app(c, core_bind(c, CORE_LAM, "g", NULL, core_bind(c, CORE_LAM, "q", NULL, core_bind(c, CORE_PLAM, path_binder(pt->name), NULL, body))), f), p);
}

/* funExt h is (fun g => fun i => fun x => g x @ i) h, for
   h : (x : A) -> PathP L a b, of type
   PathP (fun i => (x : A) -> L[i]) (fun x => a) (fun x => b). */
static const Core *rule_funext(Call *k) {
  Checker *c = k->c;
  const Value *ht = NULL;
  const Core *h = infer(c, k->args[0], &ht);
  const char *x;
  const Value *cod;
  const Value *at_x;
  const Value *inner;
  const Core *line;
  const Core *body;
  if (h == NULL)
    return NULL;
  cod = ht != NULL && ht->kind == VAL_PI ? closure_apply(c->m, ht, val_var(c->m, c->level)) : NULL;
  if (cod == NULL || cod->kind != VAL_PATHP)
    return nul(FAIL(c, "TYPE_MISMATCH", "funExt needs a function into paths (x : A) -> PathP L a b, found a term of type %s", show(c, ht)));
  x = ht->name != NULL ? ht->name : "x";
  /* The line: i at LEVEL, x at LEVEL + 1. */
  at_x = closure_apply(c->m, ht, val_var(c->m, c->level + 1u));
  /* The body: h at LEVEL, i at LEVEL + 1, x at LEVEL + 2. */
  inner = closure_apply(c->m, ht, val_var(c->m, c->level + 2u));
  if (at_x == NULL || inner == NULL || at_x->kind != VAL_PATHP || inner->kind != VAL_PATHP)
    return nul(FAIL(c, "INTERNAL", "funExt: the codomain of %s is not a path type at each argument", show(c, ht)));
  line = core_bind(c, CORE_PI, x, quote_value(c->m, c->level + 1u, ht->dom), quote_value(c->m, c->level + 2u, closure_apply(c->m, at_x, val_ivar(c->m, c->level))));
  k->type = here(c, core_ends(c, CORE_PATHP, cod->name, NULL, line, core_bind(c, CORE_LAM, x, NULL, quote_value(c->m, c->level + 1u, cod->args[0])), core_bind(c, CORE_LAM, x, NULL, quote_value(c->m, c->level + 1u, cod->args[1]))));
  body = core_ends(c, CORE_PAPP, NULL, core_app(c, core_index(c, CORE_VAR, 2), core_index(c, CORE_VAR, 0)), core_index(c, CORE_VAR, 1), quote_value(c->m, c->level + 3u, inner->args[0]), quote_value(c->m, c->level + 3u, inner->args[1]));
  return core_app(c, core_bind(c, CORE_LAM, "g", NULL, core_bind(c, CORE_PLAM, path_binder(cod->name), NULL, core_bind(c, CORE_LAM, x, NULL, body))), h);
}

/* TRANSP_LINE: the line names its interval variable in the message. */
static const Core *transp_line_fail(Checker *c, const char *name, const Value *face, const Core *line) {
  const Value *v = at(c, line, val_ivar(c->m, c->level));
  const char *f = show(c, face);
  const char *zero = show(c, at(c, line, val_iend(c->m, 0)));
  const char *bound;
  if (!push_interval(c, path_binder(name)))
    return NULL;
  bound = show(c, v);
  pop(c);
  return nul(FAIL(c, "TRANSP_LINE", "the line of transp must be constant where %s holds, but it is %s at %s and %s at i0", f, bound, path_binder(name), zero));
}

/* transp (fun i => A) phi a, with phi : I and a : A[i0], of type A[i1]
   (S2 R3 (a)). On each face of phi the line is constant: under the face
   map of each conjunction, A at a fresh i is A at i0. */
static const Core *rule_transp(Call *k) {
  Checker *c = k->c;
  uint64_t level = 0;
  const Core *line = check_line(c, k->args[0], &level);
  const Core *phi = line == NULL ? NULL : check(c, k->args[1], interval_type(c));
  const Core *a = phi == NULL ? NULL : check(c, k->args[2], at(c, line, val_iend(c->m, 0)));
  const Value *face = a == NULL ? NULL : face_norm(c->m, here(c, phi));
  const Env *e = NULL;
  uint32_t j;
  if (face == NULL)
    return NULL;
  for (j = 0; j < face->conj_count; j++) {
    if (!env_face(c->m, c->env, &face->conj[j], &e))
      return NULL;
    if (!conv_values(c->m, c->level + 1u, eval_core(c->m, env_push(c->m, e, val_ivar(c->m, c->level)), line), eval_core(c->m, env_push(c->m, e, val_iend(c->m, 0)), line)))
      return transp_line_fail(c, k->args[0]->name, face, line);
  }
  k->type = at(c, line, val_iend(c->m, 1));
  return op3(c, OP_TRANSP, 0, 3, core_bind(c, CORE_PLAM, path_binder(k->args[0]->name), NULL, line), phi, a);
}

/* A branch `k -> t` of a system: the core of its key, the face normal
   form of the key and the core of its body (under the tube binder). */
typedef struct {
  const Term *term;
  const Core *key;
  const Value *face;
  const Core *body;
} Branch;

static uint32_t system_size(const Term *sys) {
  uint32_t n = 0;
  for (; sys != NULL && sys->left != NULL; sys = sys->right)
    n++;
  return n;
}

/* The body core BODY at the interval value R, in the env E. */
static const Value *branch_at(Checker *c, const Env *e, const Core *body, const Value *r) {
  const Env *with = env_push(c->m, e, r);
  return with == NULL ? NULL : eval_core(c->m, with, body);
}

/* Split disjunctive keys before elaboration: inferred arguments can be
   different on each conjunction, so each one needs its own body core. */
static Branch *split_branches(Checker *c, const Branch *bs, uint32_t n, uint32_t *count) {
  Branch *out;
  Value *face;
  uint32_t i;
  uint32_t j;
  uint32_t k = 0;
  *count = 0;
  for (i = 0; i < n; i++)
    *count += bs[i].face->conj_count > 0 ? bs[i].face->conj_count : 1u;
  out = arena_alloc(c->m->arena, ((size_t)*count + 1u) * sizeof *out);
  if (out == NULL) {
    FAIL(c, "OOM", "out of memory");
    return NULL;
  }
  for (i = 0; i < n; i++) {
    if (bs[i].face->conj_count <= 1u) {
      out[k++] = bs[i];
      continue;
    }
    for (j = 0; j < bs[i].face->conj_count; j++) {
      face = arena_alloc(c->m->arena, sizeof *face);
      if (face == NULL) {
        FAIL(c, "OOM", "out of memory");
        return NULL;
      }
      *face = *bs[i].face;
      face->conj = &bs[i].face->conj[j];
      face->conj_count = 1;
      out[k] = bs[i];
      out[k].face = face;
      out[k].key = quote_value(c->m, c->level, face);
      if (out[k].key == NULL)
        return NULL;
      k++;
    }
  }
  return out;
}

/* The body of B against A, with the tube binder NAME, under its single
   conjunction. A key with no conjunction checks in the plain context.
   NAME is NULL for a binder that no term can use (Glue and glue). */
static const Core *hcomp_branch(Checker *c, const char *name, const Core *a, const Branch *b) {
  const Env *saved = c->env;
  const Scope *scope = c->scope;
  const Scope *s;
  Scope *copy;
  const Scope **tail;
  const Scope *acted;
  const Core *type;
  const Env *e;
  const Core *core = NULL;
  const Core *one;
  uint32_t n = b->face->conj_count > 0 ? b->face->conj_count : 1u;
  uint32_t j;
  for (j = 0; j < n; j++) {
    e = saved;
    if (b->face->conj_count > 0 && !env_face(c->m, saved, &b->face->conj[j], &e))
      return NULL;
    acted = NULL;
    tail = &acted;
    for (s = scope; s != NULL; s = s->next) {
      type = quote_value(c->m, c->level, s->type);
      copy = arena_alloc(c->m->arena, sizeof *copy);
      if (type == NULL || copy == NULL)
        return nul(c->m->diag->set ? 0 : FAIL(c, "OOM", "out of memory"));
      *copy = *s;
      copy->type = eval_core(c->m, e, type);
      if (copy->type == NULL)
        return NULL;
      *tail = copy;
      tail = &copy->next;
    }
    *tail = NULL;
    c->scope = acted;
    c->env = e;
    if (!push_interval(c, name)) {
      c->env = saved;
      c->scope = scope;
      return NULL;
    }
    one = check(c, b->term->right, eval_core(c->m, e, a));
    pop(c);
    c->env = saved;
    c->scope = scope;
    if (one == NULL)
      return NULL;
    core = core == NULL ? one : core;
  }
  return core;
}

/* SYSTEM_OVERLAP: the branches X and Y agree at a fresh i on each
   conjunction of JOINT, the meet of their faces. */
static int hcomp_overlap(Checker *c, const char *name, const Value *joint, const Branch *x, const Branch *y) {
  const Value *i = val_ivar(c->m, c->level);
  const Env *e = NULL;
  const Value *vx;
  const Value *vy;
  const char *sx;
  const char *sy;
  uint32_t j;
  if (joint == NULL)
    return 0;
  for (j = 0; j < joint->conj_count; j++) {
    if (!env_face(c->m, c->env, &joint->conj[j], &e))
      return 0;
    vx = branch_at(c, e, x->body, i);
    vy = branch_at(c, e, y->body, i);
    if (vx == NULL || vy == NULL)
      return 0;
    if (!conv_values(c->m, c->level + 1u, vx, vy)) {
      if (!push_interval(c, path_binder(name)))
        return 0;
      sx = show(c, vx);
      sy = show(c, vy);
      pop(c);
      return FAIL(c, "SYSTEM_OVERLAP", "the branches for %s and %s must agree where both keys hold, but they are %s and %s", show(c, here(c, x->key)), show(c, here(c, y->key)), sx, sy);
    }
  }
  return 1;
}

/* HCOMP_CAP: on each conjunction of the face of B, B at i0 is the base U0. */
static int hcomp_cap(Checker *c, const Core *u0, const Branch *b) {
  const Env *e = NULL;
  const Value *at0;
  const Value *base;
  uint32_t j;
  for (j = 0; j < b->face->conj_count; j++) {
    if (!env_face(c->m, c->env, &b->face->conj[j], &e))
      return 0;
    at0 = branch_at(c, e, b->body, val_iend(c->m, 0));
    base = eval_core(c->m, e, u0);
    if (at0 == NULL || base == NULL)
      return 0;
    if (!conv_values(c->m, c->level, at0, base))
      return FAIL(c, "HCOMP_CAP", "the base of hcomp must be the branch for %s at i0, but the base is %s and the branch is %s at i0", show(c, here(c, b->key)), show(c, base), show(c, at0));
  }
  return 1;
}

/* The branches of the system body of TUBE. Each key is checked against I
   and face-normalized. The join of the keys must be the face PHI
   (SYSTEM_COVER). A disjunctive key gives a branch for each conjunction
   (split_branches). *COUNT gets the number of branches. hcomp, Glue and
   glue use this. */
static Branch *system_branches(Checker *c, const Term *tube, const Value *phi, uint32_t *count) {
  uint32_t n = system_size(tube->right);
  Branch *bs = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *bs);
  const Value *join = val_iend(c->m, 0);
  const Value *pf;
  const Term *cell;
  uint32_t i;
  if (bs == NULL) {
    FAIL(c, "OOM", "out of memory");
    return NULL;
  }
  for (cell = tube->right, i = 0; i < n; cell = cell->right, i++) {
    bs[i].term = cell->left;
    bs[i].key = check(c, cell->left->left, interval_type(c));
    bs[i].face = face_norm(c->m, here(c, bs[i].key));
    if (bs[i].face == NULL)
      return NULL;
    join = face_join(c->m, join, bs[i].face);
  }
  pf = face_norm(c->m, phi);
  if (join == NULL || pf == NULL)
    return NULL;
  if (!conv_values(c->m, c->level, join, pf)) {
    FAIL(c, "SYSTEM_COVER", "the keys of the system must cover %s, but their join is %s", show(c, pf), show(c, join));
    return NULL;
  }
  return split_branches(c, bs, n, count);
}

/* SYSTEM_OVERLAP for each pair of the N checked branches BS. */
static int system_overlaps(Checker *c, const char *name, const Branch *bs, uint32_t n) {
  uint32_t i;
  uint32_t j;
  for (i = 0; i < n; i++)
    for (j = i + 1u; j < n; j++)
      if (!hcomp_overlap(c, name, face_meet(c->m, bs[i].face, bs[j].face), &bs[i], &bs[j]))
        return 0;
  return 1;
}

/* The OP_SYSTEM core of the N checked branches BS: each key, then its body
   under the path binder NAME. */
static const Core *system_core(Checker *c, const char *name, const Branch *bs, uint32_t n) {
  const Core **sys = arena_alloc(c->m->arena, (2u * (size_t)n + 1u) * sizeof *sys);
  uint32_t i;
  if (sys == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < n; i++) {
    sys[2u * i] = bs[i].key;
    sys[2u * i + 1u] = core_bind(c, CORE_PLAM, name, NULL, bs[i].body);
  }
  return core_op(c, OP_SYSTEM, 0, 0, sys, 2u * n);
}

/* hcomp A phi (fun i => [ k0 -> t0, ... ]) u0, with phi : I, each key
   k : I in the outer context, u0 : A and each branch t : A for i : I where
   its key holds (S2 R2 (a)), of type A. The keys cover phi (SYSTEM_COVER),
   two branches agree where both keys hold (SYSTEM_OVERLAP) and each branch
   at i0 is u0 (HCOMP_CAP). Hcomp at a universe is Glue (S3). A face acts
   on both the env values and the local scope types. */
static const Core *rule_hcomp(Call *k) {
  Checker *c = k->c;
  uint64_t level = 0;
  const Term *tube = k->args[2];
  const Core *a = check_type(c, k->args[0], &level);
  const Value *av = here(c, a);
  const Core *phi;
  const Core *u0;
  const Core *args[4];
  Branch *bs;
  uint32_t n = 0;
  uint32_t i;
  if (av == NULL)
    return NULL;
  if (av->kind == VAL_UNIV && av->nat != 0u)
    return nul(FAIL(c, "HCOMP_UNIVERSE", "hcomp at Type %llu needs Glue above Type 0", (unsigned long long)av->nat));
  phi = check(c, k->args[1], interval_type(c));
  if (phi == NULL)
    return NULL;
  if (tube->kind != TERM_LAM || (tube->left != NULL && !is_interval(c, tube->left)) || tube->right == NULL || tube->right->kind != TERM_SYSTEM)
    return nul(FAIL(c, "TYPE_MISMATCH", "the tube of hcomp must be a system abstraction fun (i : I) => [ phi -> t, ... ]"));
  bs = system_branches(c, tube, here(c, phi), &n);
  if (bs == NULL)
    return NULL;
  for (i = 0; i < n; i++) {
    bs[i].body = hcomp_branch(c, tube->name, a, &bs[i]);
    if (bs[i].body == NULL)
      return NULL;
  }
  if (!system_overlaps(c, tube->name, bs, n))
    return NULL;
  u0 = check(c, k->args[3], av);
  if (u0 == NULL)
    return NULL;
  for (i = 0; i < n; i++)
    if (!hcomp_cap(c, u0, &bs[i]))
      return NULL;
  args[0] = a;
  args[1] = phi;
  args[2] = system_core(c, path_binder(tube->name), bs, n);
  args[3] = u0;
  k->type = av;
  return core_op(c, OP_HCOMP, 0, 0, args, 4);
}

/* GLUE_BINDER: the tube of Glue and glue is fun (_ : I) => [ k -> t, ... ].
   The binder must be _, so a branch cannot use it and an outer i stays
   visible. The branches check under a binder with no name (see
   glue_branch), so a branch cannot use the name _ for it. */
static int glue_tube(Call *k, const Term *tube) {
  Checker *c = k->c;
  if (tube->kind != TERM_LAM || (tube->left != NULL && !is_interval(c, tube->left)) || tube->right == NULL || tube->right->kind != TERM_SYSTEM)
    return FAIL(c, "TYPE_MISMATCH", "the tube of %s must be a system abstraction fun (_ : I) => [ phi -> t, ... ]", k->b->name);
  if (tube->name != NULL && strcmp(tube->name, "_") != 0)
    return FAIL(c, "GLUE_BINDER", "the tube binder of %s must be _, found %s; a branch of %s cannot use the tube variable", k->b->name, tube->name, k->b->name);
  return 1;
}

/* Sigma (T : Type 0) (Equiv T A), the type of a Glue branch, for the type
   AV in the current context. Equiv is the domain definition. */
static const Core *equiv_sigma(Checker *c, const Value *av) {
  uint32_t d = find_def(c->m, "Equiv");
  const Core *equiv;
  if (d == NO_DEF)
    return nul(FAIL(c, "NAME_UNKNOWN", "Glue needs the domain definition Equiv, which is not declared"));
  equiv = core_app(c, core_app(c, core_index(c, CORE_GLOBAL, d), core_index(c, CORE_VAR, 0)), quote_value(c->m, c->level + 1u, av));
  return core_bind(c, CORE_SIGMA, "T", core_leaf(c, CORE_UNIV, 0), equiv);
}

/* 1 for OOM and for a failure of the evaluator. These failures are not
   about a branch, so GLUE_EQUIV does not replace them. */
static int kept_failure(const char *code) {
  return strcmp(code, "OOM") == 0 || strcmp(code, "INTERNAL") == 0 || strcmp(code, "EVAL_FUEL") == 0 || strcmp(code, "EVAL_DEPTH") == 0;
}

/* GLUE_EQUIV: the branch B of Glue A phi sys is pack T e of type SIGMA,
   that is Sigma (T : Type 0) (Equiv T A), where its key holds. A failure
   of this check becomes GLUE_EQUIV, with the first code and message. */
static const Core *glue_branch(Checker *c, const Core *sigma, const Value *av, const Branch *b) {
  char inner[sizeof c->m->diag->msg];
  const char *code;
  Diag clean = *c->m->diag;
  const Core *body = hcomp_branch(c, NULL, sigma, b);
  if (body != NULL || !c->m->diag->set)
    return body;
  code = c->m->diag->code != NULL ? c->m->diag->code : "-";
  if (kept_failure(code))
    return NULL;
  snprintf(inner, sizeof inner, "%s", c->m->diag->msg);
  *c->m->diag = clean;
  return nul(FAIL(c, "GLUE_EQUIV", "the branch for %s must be pack T e with T : Type 0 and e : Equiv T %s: %s: %s", show(c, here(c, b->key)), show(c, av), code, inner));
}

/* Glue A phi (fun (_ : I) => [ k0 -> pack T0 e0, ... ]), with A : Type 0,
   phi : I, each key k : I in the outer context and each branch of type
   Sigma (T : Type 0) (Equiv T A) where its key holds (S3b), of type
   Type 0. The keys cover phi (SYSTEM_COVER), each branch is an
   equivalence into A (GLUE_EQUIV) and two branches agree where both keys
   hold (SYSTEM_OVERLAP). The core is OP_GLUE (A, phi, sys), with sys as
   hcomp keeps it. */
static const Core *rule_glue(Call *k) {
  Checker *c = k->c;
  const Term *tube = k->args[2];
  const Core *a = check(c, k->args[0], val_univ(c->m, 0));
  const Value *av = here(c, a);
  const Core *phi = av == NULL ? NULL : check(c, k->args[1], interval_type(c));
  const Core *sigma;
  const Core *args[3];
  Branch *bs;
  uint32_t n = 0;
  uint32_t i;
  if (phi == NULL || !glue_tube(k, tube))
    return NULL;
  sigma = equiv_sigma(c, av);
  bs = sigma == NULL ? NULL : system_branches(c, tube, here(c, phi), &n);
  if (bs == NULL)
    return NULL;
  for (i = 0; i < n; i++) {
    bs[i].body = glue_branch(c, sigma, av, &bs[i]);
    if (bs[i].body == NULL)
      return NULL;
  }
  if (!system_overlaps(c, "_", bs, n))
    return NULL;
  args[0] = a;
  args[1] = phi;
  args[2] = system_core(c, "_", bs, n);
  k->type = val_univ(c->m, 0);
  return core_op(c, OP_GLUE, 0, 0, args, 3);
}

/* GLUE_BOUNDARY: on each conjunction of the face of B, unglue of the
   branch t of glue is the base A0. G is the expected Glue type. A key of G
   holds there, so unglue t is witness e t (S3b face rule). */
static int glue_boundary(Checker *c, const Value *g, const Core *a0, const Branch *b) {
  const Core *args[4];
  const Core *un;
  const Env *e = NULL;
  const Value *vu;
  const Value *va;
  uint32_t j;
  for (j = 0; j < 3u; j++)
    args[j] = quote_value(c->m, c->level + 1u, g->args[j]);
  args[3] = b->body;
  un = core_op(c, OP_UNGLUE, 0, 0, args, 4);
  if (un == NULL)
    return 0;
  for (j = 0; j < b->face->conj_count; j++) {
    if (!env_face(c->m, c->env, &b->face->conj[j], &e))
      return 0;
    vu = branch_at(c, e, un, val_iend(c->m, 1));
    va = eval_core(c->m, e, a0);
    if (vu == NULL || va == NULL)
      return 0;
    if (!conv_values(c->m, c->level, vu, va))
      return FAIL(c, "GLUE_BOUNDARY", "unglue of the branch for %s must be the base of glue where its key holds, but it is %s and the base is %s", show(c, here(c, b->key)), show(c, vu), show(c, va));
  }
  return 1;
}

/* glue (fun (_ : I) => [ k0 -> t0, ... ]) a against Glue A phi sys (S3b),
   in check mode only. The keys cover phi (SYSTEM_COVER), each branch t is
   a term of the Glue type where its key holds, that is of T, two branches
   agree where both keys hold (SYSTEM_OVERLAP), a : A and unglue t is a
   where the key of t holds (GLUE_BOUNDARY). The core is OP_GLUE_ELEM (phi,
   sys, a). */
static const Core *rule_glue_elem(Call *k) {
  Checker *c = k->c;
  const Value *g = k->hint;
  const Term *tube = k->args[0];
  const Core *gt;
  const Core *a;
  const Core *args[3];
  Branch *bs;
  uint32_t n = 0;
  uint32_t i;
  if (!val_is(g, OP_GLUE) || g->argc != 3u)
    return need_type(k, "Glue A phi sys");
  if (!glue_tube(k, tube))
    return NULL;
  gt = quote_value(c->m, c->level, g);
  bs = gt == NULL ? NULL : system_branches(c, tube, g->args[1], &n);
  if (bs == NULL)
    return NULL;
  for (i = 0; i < n; i++) {
    bs[i].body = hcomp_branch(c, NULL, gt, &bs[i]);
    if (bs[i].body == NULL)
      return NULL;
  }
  if (!system_overlaps(c, "_", bs, n))
    return NULL;
  a = check(c, k->args[1], g->args[0]);
  if (a == NULL)
    return NULL;
  for (i = 0; i < n; i++)
    if (!glue_boundary(c, g, a, &bs[i]))
      return NULL;
  args[0] = quote_value(c->m, c->level, g->args[1]);
  args[1] = system_core(c, "_", bs, n);
  args[2] = a;
  k->type = g;
  return core_op(c, OP_GLUE_ELEM, 0, 0, args, 3);
}

/* unglue g, with g of the type Glue A phi sys (S3b), of type A. The core
   keeps A, phi and sys, as p @ r keeps its ends (S1), because a neutral
   carries no type. The type of g must be a Glue type (UNGLUE_TYPE). The
   core is OP_UNGLUE (A, phi, sys, g). */
static const Core *rule_unglue(Call *k) {
  Checker *c = k->c;
  const Value *gt = NULL;
  const Core *g = infer(c, k->args[0], &gt);
  const Core *args[4];
  uint32_t i;
  if (g == NULL)
    return NULL;
  if (!val_is(gt, OP_GLUE) || gt->argc != 3u)
    return nul(FAIL(c, "UNGLUE_TYPE", "unglue needs a term of a type Glue A phi sys, found a term of type %s", show(c, gt)));
  for (i = 0; i < 3u; i++)
    args[i] = quote_value(c->m, c->level, gt->args[i]);
  args[3] = g;
  k->type = gt->args[0];
  return core_op(c, OP_UNGLUE, 0, 0, args, 4);
}

/* natAdd, natEq and the like: each argument has the type
   former ARG. natAdd gives Option ARG, none at overflow (S3). */
static const Core *rule_prim(Call *k, Op arg) {
  Checker *c = k->c;
  const Value *t = tyop(c, arg, 0, NULL, NULL, NULL);
  const Core *x = check(c, k->args[0], t);
  const Core *y = x == NULL || k->b->arity < 2u ? NULL : check(c, k->args[1], t);
  k->type = k->b->result == OP_OPTION ? tyop(c, OP_OPTION, 1, t, NULL, NULL) : tyop(c, k->b->result, 0, NULL, NULL, NULL);
  return k->b->arity < 2u ? op3(c, k->b->op, 0, 1, x, NULL, NULL) : op3(c, k->b->op, 0, 2, x, y, NULL);
}

static uint32_t find_family(const Machine *m, const char *name);

/* 1 when the type T is first-order data (S2, USER ruling Q-S2-5 (a)):
   Unit, Flag, Nat, Amount, Fin, a Prod, Sum or Option of first-order
   data, or a domain family with no parameter, no index and no path
   constructor, whose fields are the family itself or first-order data.
   Then the conversion check of the evaluator decides the equality of two
   closed values of T, and no path of T can make that equality wrong. A
   function, a path, a universe, a neutral type and a family with a path
   constructor are not first-order. DEPTH stops a cycle of families. */
static int asset_first_order(Machine *m, const Value *t, uint32_t depth) {
  const FamilyInfo *f;
  const FieldInfo *fi;
  uint32_t i;
  uint32_t j;
  if (t == NULL || depth > 64u)
    return 0;
  if (val_is(t, OP_UNIT) || val_is(t, OP_FLAG) || val_is(t, OP_NAT) || val_is(t, OP_AMOUNT) || val_is(t, OP_FIN))
    return 1;
  if (val_is(t, OP_PROD) || val_is(t, OP_SUM))
    return t->argc == 2u && asset_first_order(m, t->args[0], depth + 1u) && asset_first_order(m, t->args[1], depth + 1u);
  if (val_is(t, OP_OPTION))
    return t->argc == 1u && asset_first_order(m, t->args[0], depth + 1u);
  if (!val_is(t, OP_FAMILY) || t->inst >= m->family_count)
    return 0;
  f = &m->families[t->inst];
  if (f->param_count != 0u || f->index_count != 0u || f->block_count > 1u || f->first_ctor + f->ctor_count > m->ctor_count)
    return 0;
  for (i = f->first_ctor; i < f->first_ctor + f->ctor_count; i++) {
    if (m->ctors[i].interval_count != 0u)
      return 0;
    for (j = 0; j < m->ctors[i].field_count; j++) {
      fi = &m->ctors[i].fields[j];
      if (fi->path || fi->dependent || fi->over_recursive)
        return 0;
      if (!fi->recursive && !asset_first_order(m, eval_core(m, NULL, fi->type), depth + 1u))
        return 0;
    }
  }
  return 1;
}

/* valueCount A v a (S2, USER ruling Q-S2-5 (a)): the count of a in the
   bag v : Bag A, an Amount. A C builtin (eval only, as len): the
   conversion check of the evaluator is the equality on A, so A must be
   first-order data (REFUSE_SIG: the Asset slot form, PLAN section 4). */
static const Core *rule_value_count(Call *k) {
  Checker *c = k->c;
  uint32_t fam = find_family(c->m, "Bag");
  const Core *args[3];
  const Value *a;
  k->type = tyop(c, OP_AMOUNT, 0, NULL, NULL, NULL);
  args[0] = check(c, k->args[0], val_univ(c->m, 0));
  a = here(c, args[0]);
  if (a != NULL && !asset_first_order(c->m, a, 0u))
    return nul(FAIL(c, "REFUSE_SIG", "valueCount needs a first-order element type, not %s: no path constructor and no function (PLAN section 4, USER ruling Q-S2-5 (a))", show(c, a)));
  args[1] = a == NULL || fam >= c->m->family_count ? NULL : check(c, k->args[1], val_op(c->m, VAL_OP, OP_FAMILY, fam, 0, &a, 1));
  args[2] = args[1] == NULL ? NULL : check(c, k->args[2], a);
  return args[2] == NULL ? NULL : core_op(c, OP_VALUE_COUNT, 0, 0, args, 3);
}

/* len A r (S3, USER ruling Q-S3-3 (a)): the op count of the trace
   r : FreeMon A, a Nat (an OpPos). A C builtin: the domain cannot prove
   the Nat monoid laws that fmFold needs (S3 survey section 7). */
static const Core *rule_len(Call *k) {
  Checker *c = k->c;
  uint32_t fam = find_family(c->m, "FreeMon");
  const Core *args[2];
  const Value *a;
  args[0] = check(c, k->args[0], val_univ(c->m, 0));
  a = here(c, args[0]);
  args[1] = a == NULL || fam >= c->m->family_count ? NULL : check(c, k->args[1], val_op(c->m, VAL_OP, OP_FAMILY, fam, 0, &a, 1));
  k->type = tyop(c, OP_NAT, 0, NULL, NULL, NULL);
  return args[1] == NULL ? NULL : core_op(c, OP_FM_LEN, 0, 0, args, 2);
}

/* Fin n: n : Nat, Fin n : Type 0. */
static const Core *rule_fin(Call *k) {
  const Core *n = check(k->c, k->args[0], nat_type(k->c));
  k->type = val_univ(k->c->m, 0);
  return op3(k->c, OP_FIN, 0, 1, n, NULL, NULL);
}

/* finAdd n a b, finNeg n a: n : Nat, each other argument : Fin n, the
   result : Fin n. */
static const Core *rule_fin_op(Call *k) {
  Checker *c = k->c;
  const Core *n = check(c, k->args[0], nat_type(c));
  const Value *fin = n == NULL ? NULL : tyop(c, OP_FIN, 1, here(c, n), NULL, NULL);
  const Core *x = fin == NULL ? NULL : check(c, k->args[1], fin);
  const Core *y = x == NULL || k->b->arity < 3u ? NULL : check(c, k->args[2], fin);
  k->type = fin;
  return op3(c, k->b->op, 0, k->b->arity, n, x, y);
}

/* The base type of NonZero (S3): Nat. quotient-lang has no
   U256, so accrue NonZero U256 and mulDiv are not taken. */
static int nonzero_base(const Value *t) {
  return val_is(t, OP_NAT);
}

/* NonZero A (S3): A is Nat, NonZero A : Type 0. */
static const Core *rule_nonzero(Call *k) {
  const Core *t = rule_type1(k);
  const Value *v = here(k->c, t);
  if (v == NULL)
    return NULL;
  if (!nonzero_base(v->args[0]))
    return nul(FAIL(k->c, "TYPE_MISMATCH", "NonZero takes Nat, found %s", show(k->c, v->args[0])));
  return t;
}

/* nonZero x: x : Nat, the result Option (NonZero Nat). */
static const Core *rule_nonzero_of(Call *k) {
  Checker *c = k->c;
  const Value *a = val_is(k->hint, OP_OPTION) && val_is(k->hint->args[0], OP_NONZERO) ? k->hint->args[0]->args[0] : NULL;
  const Core *x = a != NULL ? check(c, k->args[0], a) : infer(c, k->args[0], &a);
  if (x == NULL)
    return NULL;
  if (!nonzero_base(a))
    return nul(FAIL(c, "TYPE_MISMATCH", "nonZero needs a Nat, found a term of type %s", show(c, a)));
  k->type = tyop(c, OP_OPTION, 1, tyop(c, OP_NONZERO, 1, a, NULL, NULL), NULL, NULL);
  return op3(c, OP_NONZERO_OF, 0, 1, x, NULL, NULL);
}

/* nonZeroValue x: x : NonZero Nat, the result Nat. */
static const Core *rule_nonzero_value(Call *k) {
  Checker *c = k->c;
  const Value *t = nonzero_base(k->hint) ? tyop(c, OP_NONZERO, 1, k->hint, NULL, NULL) : NULL;
  const Core *x = t != NULL ? check(c, k->args[0], t) : infer(c, k->args[0], &t);
  if (x == NULL)
    return NULL;
  if (!val_is(t, OP_NONZERO))
    return nul(FAIL(c, "TYPE_MISMATCH", "nonZeroValue needs a term of type NonZero Nat, found a term of type %s", show(c, t)));
  k->type = t->args[0];
  return op3(c, OP_NONZERO_VALUE, 0, 1, x, NULL, NULL);
}

/* natDiv a d and natMod a d (S3): d : NonZero Nat, the
   result Nat. The divisor type makes each one total. */
static const Core *rule_div(Call *k) {
  Checker *c = k->c;
  const Value *base = tyop(c, OP_NAT, 0, NULL, NULL, NULL);
  const Core *x = check(c, k->args[0], base);
  const Core *d = x == NULL ? NULL : check(c, k->args[1], tyop(c, OP_NONZERO, 1, base, NULL, NULL));
  k->type = base;
  return op3(c, k->b->op, 0, 2, x, d, NULL);
}

/* flagIf b yes no */
static const Core *rule_flag_if(Call *k) {
  Checker *c = k->c;
  const Value *res = k->hint;
  const Core *b = check(c, k->args[0], flag_type(c));
  const Core *yes = b == NULL ? NULL : (res != NULL ? check(c, k->args[1], res) : infer(c, k->args[1], &res));
  const Core *no = yes == NULL ? NULL : check(c, k->args[2], res);
  k->type = res;
  return op3(c, OP_FLAG_IF, 0, 3, b, yes, no);
}

static int kmap_word(const Value *t, int flag_ok) {
  return val_is(t, OP_NAT) || (flag_ok && val_is(t, OP_FLAG));
}

/* Map K V (slice K4a0): K is Nat. V is Nat or Flag. */
static const Core *rule_kmap(Call *k) {
  const Core *t = rule_type2(k);
  const Value *v = here(k->c, t);
  if (v == NULL)
    return NULL;
  if (!kmap_word(v->args[0], 0))
    return nul(FAIL(k->c, "REFUSE_MAP", "the key type of a Map must be Nat, found %s", show(k->c, v->args[0])));
  if (!kmap_word(v->args[1], 1))
    return nul(FAIL(k->c, "REFUSE_MAP", "the value type of a Map must be Nat or Flag, found %s", show(k->c, v->args[1])));
  return t;
}

/* mapGet m k and mapSet m k v (slice K4a0). The core puts V first, so the
   evaluator can make the zero value of V. */
static const Core *kmap_access(Call *k, int set) {
  Checker *c = k->c;
  const Value *t = set && val_is(k->hint, OP_KMAP) ? k->hint : NULL;
  const Core *map = t != NULL ? check(c, k->args[0], t) : infer(c, k->args[0], &t);
  const Core *key;
  const Core *args[4];
  if (map == NULL)
    return NULL;
  if (!val_is(t, OP_KMAP))
    return nul(FAIL(c, "TYPE_MISMATCH", "%s needs a Map K V, found %s", k->b->name, show(c, t)));
  key = check(c, k->args[1], t->args[0]);
  args[0] = op3(c, t->args[1]->op, 0, 0, NULL, NULL, NULL);
  args[1] = map;
  args[2] = key;
  args[3] = set && key != NULL ? check(c, k->args[2], t->args[1]) : NULL;
  k->type = set ? t : t->args[1];
  return core_op(c, k->b->op, 0, 0, args, set ? 4u : 3u);
}

static const Core *rule(Call *k) {
  switch (k->b->rule) {
  case RULE_TYPE0:
    k->type = val_univ(k->c->m, 0);
    return op3(k->c, k->b->op, 0, 0, NULL, NULL, NULL);
  case RULE_VALUE0:
    k->type = tyop(k->c, k->b->result, 0, NULL, NULL, NULL);
    return op3(k->c, k->b->op, 0, 0, NULL, NULL, NULL);
  case RULE_TYPE1:
    return rule_type1(k);
  case RULE_TYPE2:
    return rule_type2(k);
  case RULE_INTERVAL:
    return nul(FAIL(k->c, "INTERVAL_TYPE", "I is the interval, not a type; only a path abstraction or a PathP line can bind an interval variable (rule R9)"));
  case RULE_IEND:
    k->type = interval_type(k->c);
    return new_core(k->c, k->b->part == 0u ? CORE_IZERO : CORE_IONE);
  case RULE_PATHP:
    return rule_pathp(k);
  case RULE_PATH:
    return rule_path(k);
  case RULE_PAIR:
    return rule_pair(k);
  case RULE_INJ:
    return rule_inj(k);
  case RULE_EMPTY:
    return rule_empty(k);
  case RULE_SOME:
    return rule_some(k);
  case RULE_CONS:
    return rule_cons(k);
  case RULE_PACK:
    return rule_pack(k);
  case RULE_REFL:
    return rule_refl(k);
  case RULE_PART:
    return rule_part(k);
  case RULE_SIGMA_PART:
    return rule_sigma_part(k);
  case RULE_EITHER:
    return rule_either(k);
  case RULE_ELIM:
    return rule_elim(k);
  case RULE_OPTION:
    return rule_option(k);
  case RULE_PURE:
    return rule_pure(k);
  case RULE_MAP:
    return rule_map(k);
  case RULE_BIND:
    return rule_bind(k);
  case RULE_STEP_LET:
    return rule_step_let(k);
  case RULE_FILTER:
    return rule_filter(k);
  case RULE_FOLD:
    return rule_fold(k);
  case RULE_UNFOLD:
    return rule_unfold(k);
  case RULE_SYM:
    return rule_sym(k);
  case RULE_CONG:
    return rule_cong(k);
  case RULE_FUNEXT:
    return rule_funext(k);
  case RULE_TRANSP:
    return rule_transp(k);
  case RULE_HCOMP:
    return rule_hcomp(k);
  case RULE_GLUE:
    return rule_glue(k);
  case RULE_GLUE_ELEM:
    return rule_glue_elem(k);
  case RULE_UNGLUE:
    return rule_unglue(k);
  case RULE_NAT2:
    return rule_prim(k, OP_NAT);
  case RULE_AMOUNT2:
    return rule_prim(k, OP_AMOUNT);
  case RULE_LEN:
    return rule_len(k);
  case RULE_VALUE_COUNT:
    return rule_value_count(k);
  case RULE_FIN_OP:
    return rule_fin_op(k);
  case RULE_FIN:
    return rule_fin(k);
  case RULE_FLAG_IF:
    return rule_flag_if(k);
  case RULE_NONZERO:
    return rule_nonzero(k);
  case RULE_NONZERO_OF:
    return rule_nonzero_of(k);
  case RULE_NONZERO_VALUE:
    return rule_nonzero_value(k);
  case RULE_DIV:
    return rule_div(k);
  case RULE_KMAP:
    return rule_kmap(k);
  case RULE_KMAP_GET:
    return kmap_access(k, 0);
  case RULE_KMAP_SET:
    return kmap_access(k, 1);
  }
  return NULL;
}

/* Checks the first N family arguments ARGS: the parameters, then the
   indices (S6), each at the values of the arguments before it. VALS gets
   their values. */
static int check_params(Checker *c, const FamilyInfo *f, uint32_t n, const Term *const *args, const Core **cores, const Value **vals) {
  uint32_t i;
  for (i = 0; i < n; i++) {
    const Core *t = i < f->param_count ? f->param_types[i] : f->index_types[i - f->param_count];
    cores[i] = check(c, args[i], eval_core(c->m, env_of(c, vals, i), t));
    vals[i] = here(c, cores[i]);
    if (vals[i] == NULL)
      return 0;
  }
  return 1;
}

static const Core *family_app(Call *k, uint32_t fam) {
  Checker *c = k->c;
  const FamilyInfo *f = &c->m->families[fam];
  uint32_t n = f->param_count + f->index_count;
  const Core **cores = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *cores);
  const Value **vals = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *vals);
  if (cores == NULL || vals == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  if (!check_params(c, f, n, k->args, cores, vals))
    return NULL;
  k->type = val_univ(c->m, f->universe);
  return core_op(c, OP_FAMILY, fam, 0, cores, n);
}

/* A constructor takes the family parameters (the indices), then its fields,
   then its interval arguments (a path constructor). */
static const Core *ctor_app(Call *k, uint32_t ctor) {
  Checker *c = k->c;
  const CtorInfo *ci = &c->m->ctors[ctor];
  const FamilyInfo *f = &c->m->families[ci->family];
  uint32_t p = f->param_count;
  uint32_t q = p + ci->field_count;
  uint32_t n = q + ci->interval_count;
  const Core **cores = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *cores);
  const Value **vals = arena_alloc(c->m->arena, ((size_t)p + f->index_count + 1u) * sizeof *vals);
  const Env *env;
  uint32_t j;
  if (cores == NULL || vals == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  if (!check_params(c, f, p, k->args, cores, vals))
    return NULL;
  env = env_of(c, vals, p);
  /* Field j is checked at the parameters and the earlier field values. */
  for (j = 0; j < ci->field_count; j++) {
    const Value *fv;
    cores[p + j] = check(c, k->args[p + j], eval_core(c->m, env, ci->fields[j].type));
    fv = here(c, cores[p + j]);
    env = fv == NULL ? NULL : env_push(c->m, env, fv);
    if (env == NULL)
      return NULL;
  }
  for (j = q; j < n; j++) {
    cores[j] = check(c, k->args[j], interval_type(c));
    if (cores[j] == NULL)
      return NULL;
  }
  /* The result indices at the parameters and the field values (S6). */
  for (j = 0; ci->result != NULL && j < f->index_count; j++) {
    vals[p + j] = eval_core(c->m, env, ci->result[j]);
    if (vals[p + j] == NULL)
      return NULL;
  }
  k->type = val_op(c->m, VAL_OP, OP_FAMILY, ci->family, 0, vals, ci->result == NULL ? p : p + f->index_count);
  return core_op(c, OP_CTOR, ctor, 0, cores, n);
}

/* A field of a one-constructor family is a projection. */
static const Core *proj_app(Call *k, uint32_t ctor, uint32_t field) {
  Checker *c = k->c;
  const CtorInfo *ci = &c->m->ctors[ctor];
  const Value *xt = NULL;
  const Core *x = infer(c, k->args[0], &xt);
  const Env *env;
  uint32_t i;
  if (x == NULL)
    return NULL;
  if (!val_is(xt, OP_FAMILY) || xt->inst != ci->family)
    return nul(FAIL(c, "TYPE_MISMATCH", "%s needs a value of the family %s, found a term of type %s", ci->fields[field].name, c->m->families[ci->family].name, show(c, xt)));
  /* The field type at the parameters and the projections of the earlier
     fields of X (S4 item 13), as the second part of a Sigma. */
  env = env_of(c, xt->args, c->m->families[ci->family].param_count);
  for (i = 0; i < field; i++) {
    const Value *fv = here(c, core_op(c, OP_PROJ, ctor, i, &x, 1));
    env = fv == NULL ? NULL : env_push(c->m, env, fv);
    if (env == NULL)
      return NULL;
  }
  k->type = eval_core(c->m, env, ci->fields[field].type);
  return core_op(c, OP_PROJ, ctor, field, &x, 1);
}

static int find_known(Checker *c, const char *name, Head *h) {
  const Machine *m = c->m;
  uint32_t i;
  uint32_t j;
  for (i = 0; i < m->family_count; i++) {
    if (strcmp(m->families[i].name, name) == 0) {
      h->kind = HEAD_FAMILY;
      h->index = i;
      c->self_uses += in_block(c, i);
      return 1;
    }
  }
  for (i = 0; i < m->ctor_count; i++) {
    /* A reserved slot of a block has no name yet (S6). */
    if (m->ctors[i].name != NULL && strcmp(m->ctors[i].name, name) == 0) {
      h->kind = HEAD_CTOR;
      h->index = i;
      return 1;
    }
  }
  for (i = 0; i < m->ctor_count; i++) {
    /* Record projections require a point constructor. A path constructor
       can reduce to its boundary before a projection can select a field. */
    for (j = 0; m->families[m->ctors[i].family].ctor_count == 1u && m->ctors[i].interval_count == 0u && j < m->ctors[i].field_count; j++) {
      if (strcmp(m->ctors[i].fields[j].name, name) == 0) {
        h->kind = HEAD_PROJ;
        h->index = i;
        h->field = j;
        return 1;
      }
    }
  }
  for (i = 0; i < BUILTIN_COUNT; i++) {
    if (strcmp(BUILTINS[i].name, name) == 0) {
      h->kind = HEAD_BUILTIN;
      h->builtin = &BUILTINS[i];
      return 1;
    }
  }
  return 0;
}

static int guest(const Checker *c);

/* A partial name (S3): the kit has no
   total word with this name. KIT is the hint for the kit mode and the
   domain file. GUEST is the hint for a guest program. */
typedef struct {
  const char *name;
  const char *kit;
  const char *guest;
} PartialName;

static const PartialName PARTIAL_NAMES[] = {
  {"div", "use natDiv x d, with d : NonZero Nat from nonZero", "domain/domain.lang has no division for a guest program"},
  {"mod", "use natMod x d, with d : NonZero Nat from nonZero", "domain/domain.lang has no remainder for a guest program"},
  {"sub", "use natSub x y, which gives 0 when y is more than x", "domain/domain.lang has no subtraction for a guest program"},
  {"mul", "the kit has no total word for a product", "domain/domain.lang has no product for a guest program"},
  {"head", "use fold (fun x acc => some x) none on the list, which gives an Option", "domain/domain.lang has no head word for a guest program"},
  {"tail", "use fold on the list into an Option; the kit has no tail word", "domain/domain.lang has no tail word for a guest program"},
  {"pred", "use natSub x 1, which gives 0 at 0", "domain/domain.lang has no predecessor word for a guest program"}
};

#define PARTIAL_NAME_COUNT ((uint32_t)(sizeof PARTIAL_NAMES / sizeof PARTIAL_NAMES[0]))

/* The hint for a partial name, or NULL. */
static const char *partial_hint(const Checker *c, const char *name) {
  uint32_t i;
  for (i = 0; i < PARTIAL_NAME_COUNT; i++) {
    if (strcmp(PARTIAL_NAMES[i].name, name) == 0)
      return guest(c) ? PARTIAL_NAMES[i].guest : PARTIAL_NAMES[i].kit;
  }
  return NULL;
}

/* An unknown name. When it names this declaration or a later one, the use
   is recursion (rule R3). Else a partial name gives REFUSE_PARTIAL. */
static int unknown_name(Checker *c, const char *name) {
  size_t i;
  const char *hint = partial_hint(c, name);
  if (time_word(name))
    return FAIL(c, "REFUSE_TIME", TIME_HINT, name);
  for (i = c->decl_index; i < c->decls->count; i++) {
    if (strcmp(c->decls->items[i].name, name) == 0)
      return FAIL(c, "REFUSE_REC", "%s is this definition or a later one; a definition can use only earlier ones (rule R3)", name);
  }
  if (hint != NULL)
    return FAIL(c, "REFUSE_PARTIAL", "%s is a partial name: %s", name, hint);
  return FAIL(c, "NAME_UNKNOWN", "unknown name %s", name);
}

/* A program declaration in guest mode (orbit-lang S3). The domain file and
   the kit prelude are the trusted scope: no kit refusal there. */
static int guest(const Checker *c) {
  return c->mode == CHECK_GUEST && c->decls->items[c->decl_index].origin == ORIGIN_PROGRAM;
}

static int kit_refused(Checker *c, const char *what) {
  return FAIL(c, "REFUSE_KIT", "%s is a kit item outside the base span (PLAN section 4); only the kit mode langc --kit admits it", what);
}

/* An INTERNAL core name, or a family, constructor or field of origin
   ORIGIN_KIT (no source has that origin after S2). */
static int kit_head(const Checker *c, const Head *h) {
  const Machine *m = c->m;
  uint32_t fam = NO_FAMILY;
  switch (h->kind) {
  case HEAD_TERM:
    return 0;
  case HEAD_BUILTIN:
    return h->builtin->vis == VIS_INTERNAL;
  case HEAD_FAMILY:
    fam = h->index;
    break;
  case HEAD_CTOR:
  case HEAD_PROJ:
    fam = m->ctors[h->index].family;
    break;
  }
  return fam != NO_FAMILY && m->families[fam].origin == ORIGIN_KIT;
}

/* Name resolution order: locals (the innermost first), definitions,
   families, constructors, projections, core names. */
static int resolve_head(Checker *c, const Term *head, Head *h) {
  memset(h, 0, sizeof *h);
  h->kind = HEAD_TERM;
  if (head->kind != TERM_VAR || find_local(c, head->name) != NULL || find_def(c->m, head->name) != NO_DEF)
    return 1;
  if (!find_known(c, head->name, h))
    return unknown_name(c, head->name);
  if (guest(c) && h->kind == HEAD_BUILTIN && h->builtin->vis == VIS_CELL)
    return FAIL(c, "REFUSE_CELL", "%s is a cons-list name, not a cell monad; a guest program uses FreeMon of domain/domain.lang (rule R1)", head->name);
  return guest(c) && kit_head(c, h) ? kit_refused(c, head->name) : 1;
}

/* A Nat literal is a kit item (orbit-lang S3). */
static int literal_ok(Checker *c, const char *what) {
  return guest(c) ? kit_refused(c, what) : 1;
}

static uint32_t known_arity(const Checker *c, const Head *h) {
  const CtorInfo *ci = h->kind == HEAD_CTOR ? &c->m->ctors[h->index] : NULL;
  switch (h->kind) {
  case HEAD_TERM:
    return 0u;
  case HEAD_FAMILY:
    return c->m->families[h->index].param_count + c->m->families[h->index].index_count;
  case HEAD_CTOR:
    return ci == NULL ? 0u : c->m->families[ci->family].param_count + ci->field_count + ci->interval_count;
  case HEAD_PROJ:
    return 1u;
  case HEAD_BUILTIN:
    return h->builtin->arity;
  }
  return 0u;
}

static const char *known_name(const Checker *c, const Head *h) {
  switch (h->kind) {
  case HEAD_TERM:
    return "?";
  case HEAD_FAMILY:
    return c->m->families[h->index].name;
  case HEAD_CTOR:
    return c->m->ctors[h->index].name;
  case HEAD_PROJ:
    return c->m->ctors[h->index].fields[h->field].name;
  case HEAD_BUILTIN:
    return h->builtin->name;
  }
  return "?";
}

static const Core *known_core(Call *k, const Head *h) {
  switch (h->kind) {
  case HEAD_TERM:
    return nul(FAIL(k->c, "INTERNAL", "a plain term reached the core name rules"));
  case HEAD_FAMILY:
    return family_app(k, h->index);
  case HEAD_CTOR:
    return ctor_app(k, h->index);
  case HEAD_PROJ:
    return proj_app(k, h->index, h->field);
  case HEAD_BUILTIN:
    return rule(k);
  }
  return NULL;
}

/* An under-applied core name checked against a function type: WHOLE becomes
   `fun x => WHOLE x`, with a name that the lexer cannot make. */
static const Core *eta(Checker *c, const Term *whole, const Value *hint, const Value **type) {
  char *name = arena_alloc(c->m->arena, 24);
  Term *x = arena_alloc(c->m->arena, sizeof *x);
  Term *app = arena_alloc(c->m->arena, sizeof *app);
  Term *lam = arena_alloc(c->m->arena, sizeof *lam);
  if (name == NULL || x == NULL || app == NULL || lam == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  c->eta_count++;
  snprintf(name, 24, "%%eta%u", c->eta_count);
  x->kind = TERM_VAR;
  x->name = name;
  app->kind = TERM_APP;
  app->left = whole;
  app->right = x;
  lam->kind = TERM_LAM;
  lam->name = name;
  lam->right = app;
  return check_lam(c, lam, hint, type);
}

/* Applies K of type TY to ARGS, one by one. */
static const Core *apply_rest(Checker *c, const Core *k, const Value *ty, const Term *const *args, uint32_t argc, const Value *hint, const Value **type) {
  uint32_t i;
  for (i = 0; i < argc && k != NULL; i++) {
    const Core *a;
    if (ty == NULL || ty->kind != VAL_PI)
      return nul(FAIL(c, "TYPE_NOT_FUNCTION", "a term of type %s is applied to an argument", show(c, ty)));
    a = check(c, args[i], ty->dom);
    ty = closure_apply(c->m, ty, here(c, a));
    k = core_app(c, k, a);
  }
  *type = ty;
  return finish(c, k, hint, type);
}

static const Core *var_core(Checker *c, const char *name, const Value **type) {
  const Scope *s = find_local(c, name);
  uint32_t d = find_def(c->m, name);
  if (s != NULL) {
    *type = s->type;
    if (s->level >= c->field_base && s->level < c->field_top) {
      c->field_dep = 1;
      c->field_rec |= val_is(s->type, OP_FAMILY) && in_block(c, s->type->inst);
    }
    return core_index(c, CORE_VAR, c->level - 1u - s->level);
  }
  if (d != NO_DEF) {
    *type = c->m->defs[d].type;
    return core_index(c, CORE_GLOBAL, d);
  }
  if (time_word(name))
    return nul(FAIL(c, "REFUSE_TIME", TIME_HINT, name));
  if (partial_hint(c, name) != NULL)
    return nul(FAIL(c, "REFUSE_PARTIAL", "%s is a partial name: %s", name, partial_hint(c, name)));
  return nul(FAIL(c, "NAME_UNKNOWN", "unknown name %s", name));
}

static const Core *apply_term(Checker *c, const Term *head, const Term *const *args, uint32_t argc, const Value *hint, const Value **type) {
  const Value *ty = NULL;
  const Core *k = head->kind == TERM_VAR ? var_core(c, head->name, &ty) : infer(c, head, &ty);
  return apply_rest(c, k, ty, args, argc, hint, type);
}

/* REFUSE_PARTIAL site 2 (S3): a checked kit word
   gives an Option, and the term is where its payload type is wanted. A
   guest program cannot name a kit word (REFUSE_KIT comes first). 1 when
   the term is not this case. */
static int partial_result_ok(Checker *c, const Head *h, const Value *found, const Value *want) {
  if (h->kind != HEAD_BUILTIN || h->builtin->vis != VIS_INTERNAL || h->builtin->result != OP_OPTION)
    return 1;
  if (found == NULL || want == NULL || !val_is(found, OP_OPTION) || val_is(want, OP_OPTION))
    return 1;
  if (!conv_values(c->m, c->level, found->args[0], want))
    return 1;
  return FAIL(c, "REFUSE_PARTIAL", "%s gives an Option, not a value of type %s: take it apart with option or bind", known_name(c, h), show(c, want));
}

/* REFUSE_OVERFLOW (S2, USER ruling Q-S2-2 (a)): amountAdd and amountSub
   give Maybe Amount (none at overflow and at underflow), and the term is
   where an Amount is wanted. 1 when the term is not this case. */
static int overflow_result_ok(Checker *c, const Head *h, const Value *found, const Value *want) {
  if (h->kind != HEAD_BUILTIN || (h->builtin->op != OP_AMOUNT_ADD && h->builtin->op != OP_AMOUNT_SUB))
    return 1;
  if (found == NULL || want == NULL || !val_is(found, OP_OPTION) || val_is(want, OP_OPTION))
    return 1;
  if (!conv_values(c->m, c->level, found->args[0], want))
    return 1;
  return FAIL(c, "REFUSE_OVERFLOW", "%s gives Maybe Amount (none at overflow or at underflow), not a value of type %s: take it apart with option or bind", known_name(c, h), show(c, want));
}

static const Core *apply_known(Checker *c, const Term *whole, const Head *h, const Term *const *args, uint32_t argc, const Value *hint, const Value **type) {
  uint32_t arity = known_arity(c, h);
  Call k;
  const Core *core;
  if (h->kind == HEAD_BUILTIN && h->builtin->rule == RULE_ELIM && argc >= 3u &&
      hint != NULL && hint->kind == VAL_PI) {
    const Value *pt = NULL;
    const Value *dom = NULL;
    uint32_t d = 0;
    /* An indexed motive starts with its indices, so its first binder
       does not determine the number of constructor cases. */
    if (try_infer(c, args[0], &pt) != NULL) {
      Diag saved = *c->m->diag;
      dom = motive_domain(c, pt, &d);
      *c->m->diag = saved;
    }
    if (dom == NULL)
      dom = elim_domain(c, args, argc);
    /* A bare motive can acquire its domain from the scrutinee after eta. */
    if (dom == NULL)
      return eta(c, whole, hint, type);
    if (val_is(dom, OP_SUM))
      arity = 4u;
    else if (val_is(dom, OP_FAMILY))
      arity = c->m->families[dom->inst].ctor_count + 2u;
  }
  if (argc < arity && hint != NULL && hint->kind == VAL_PI)
    return eta(c, whole, hint, type);
  if (argc < arity)
    return nul(FAIL(c, "TYPE_ARITY", "%s needs %u arguments, found %u", known_name(c, h), arity, argc));
  memset(&k, 0, sizeof k);
  k.c = c;
  k.b = h->builtin;
  k.args = args;
  k.argc = argc;
  k.hint = argc == arity ? hint : NULL;
  k.outer = hint;
  k.used = arity;
  core = known_core(&k, h);
  if (core != NULL && argc == k.used && (!partial_result_ok(c, h, k.type, hint) || !overflow_result_ok(c, h, k.type, hint)))
    return NULL;
  return apply_rest(c, core, k.type, args + k.used, argc - k.used, hint, type);
}

static const Core *elab_spine(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Term **args;
  const Term *head = t;
  uint32_t argc = 0;
  uint32_t i;
  Head h;
  while (head->kind == TERM_APP) {
    argc++;
    head = head->left;
  }
  if (argc > SPINE_MAX)
    return nul(FAIL(c, "TYPE_ARITY", "an application has more than %u arguments", SPINE_MAX));
  args = arena_alloc(c->m->arena, ((size_t)argc + 1u) * sizeof *args);
  if (args == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  for (head = t, i = argc; head->kind == TERM_APP; head = head->left)
    args[--i] = head->right;
  if (!resolve_head(c, head, &h))
    return NULL;
  return h.kind == HEAD_TERM ? apply_term(c, head, args, argc, hint, type) : apply_known(c, t, &h, args, argc, hint, type);
}

/* Retain the checked syntax before conversion erases law-only references. */
static const Core *checked_annotation(Checker *c, const Term *ann, const Value *dom) {
  uint64_t level = 0;
  const Core *a = check_type(c, ann, &level);
  const Value *v = here(c, a);
  if (v == NULL)
    return NULL;
  return conv_values(c->m, c->level, v, dom) ? a : nul(FAIL(c, "TYPE_MISMATCH", "the binder type %s differs from the expected type %s", show(c, v), show(c, dom)));
}

/* A path abstraction against the path type HINT: the body at the interval
   variable, then the ends at i0 and i1. */
static const Core *check_plam(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Core *body;
  if (t->left != NULL && !is_interval(c, t->left))
    return nul(FAIL(c, "TYPE_MISMATCH", "a term of type %s is a path; its binder must be an interval variable fun (%s : I) => ...", show(c, hint), t->name));
  if (!push_interval(c, t->name))
    return NULL;
  body = check(c, t->right, closure_apply(c->m, hint, c->env->value));
  pop(c);
  if (body == NULL || !path_ends(c, hint, at(c, body, val_iend(c->m, 0)), at(c, body, val_iend(c->m, 1))))
    return NULL;
  *type = hint;
  return core_bind(c, CORE_PLAM, t->name, NULL, body);
}

/* fun (i : I) => t with no expected type: PathP (fun i => T) t[i0] t[i1]. */
static const Core *infer_plam(Checker *c, const Term *t, const Value **type) {
  const Value *bt = NULL;
  const Core *body;
  if (!push_interval(c, t->name))
    return NULL;
  body = infer(c, t->right, &bt);
  pop(c);
  if (body == NULL)
    return NULL;
  if (bt == NULL || val_is(bt, OP_INTERVAL))
    return nul(FAIL(c, "INTERVAL_TYPE", "the path fun (%s : I) => ... has values in I; the line of a path must be a type (rule R9)", t->name));
  *type = here(c, core_ends(c, CORE_PATHP, t->name, NULL, quote_value(c->m, c->level + 1u, bt), quote_value(c->m, c->level, at(c, body, val_iend(c->m, 0))), quote_value(c->m, c->level, at(c, body, val_iend(c->m, 1)))));
  return core_bind(c, CORE_PLAM, t->name, NULL, body);
}

/* The literal bound of a Fin n domain, or 0 when there is no finAll: the
   bound must leave room for the k argument in the uint32_t arity. */
static uint64_t fin_cases(const Value *dom) {
  if (!val_is(dom, OP_FIN) || dom->args[0]->kind != VAL_NAT || dom->args[0]->nat >= UINT32_MAX)
    return 0;
  return dom->args[0]->nat;
}

/* finAll (S3a): the body at each literal j below n, with the binder bound
   to j. The core is OP_FIN_CASE (k, body0, ..., body(n-1)). */
static const Core *check_fin_all(Checker *c, const Term *t, const Value *hint, uint64_t n) {
  const Core **args = arena_alloc(c->m->arena, ((size_t)n + 1u) * sizeof *args);
  char inner[sizeof c->m->diag->msg];
  const char *code;
  Diag clean = *c->m->diag;
  uint64_t j;
  if (args == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  args[0] = core_index(c, CORE_VAR, 0);
  for (j = 0; j < n; j++) {
    const Value *x = val_nat(c->m, j);
    if (!push_value(c, t->name, hint->dom, x))
      return NULL;
    args[j + 1u] = check(c, t->right, closure_apply(c->m, hint, x));
    pop(c);
    if (args[j + 1u] == NULL) {
      code = c->m->diag->code != NULL ? c->m->diag->code : "-";
      if (strcmp(code, "OOM") == 0)
        return NULL;
      snprintf(inner, sizeof inner, "%s", c->m->diag->msg);
      *c->m->diag = clean;
      return nul(FAIL(c, "FIN_CASE", "the case %llu of Fin %llu fails: %s: %s", (unsigned long long)j, (unsigned long long)n, code, inner));
    }
  }
  return core_op(c, OP_FIN_CASE, 0, 0, args, (uint32_t)n + 1u);
}

static const Core *check_lam(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Core *body;
  const Core *ann = NULL;
  Diag clean;
  if (hint->kind == VAL_PATHP)
    return check_plam(c, t, hint, type);
  if (hint->kind != VAL_PI)
    return nul(FAIL(c, "TYPE_MISMATCH", "a function is not a term of type %s", show(c, hint)));
  if (t->left != NULL && (ann = checked_annotation(c, t->left, hint->dom)) == NULL)
    return NULL;
  clean = *c->m->diag;
  if (!push(c, t->name, hint->dom))
    return NULL;
  body = check(c, t->right, closure_apply(c->m, hint, c->env->value));
  pop(c);
  /* finAll: the ordinary check failed on a Fin n domain (literal n), so
     check each case. The ordinary core stays when the ordinary check passes. */
  if (body == NULL && fin_cases(hint->dom) > 0 && strcmp(c->m->diag->code != NULL ? c->m->diag->code : "-", "OOM") != 0) {
    *c->m->diag = clean;
    body = check_fin_all(c, t, hint, fin_cases(hint->dom));
  }
  *type = hint;
  return core_bind(c, CORE_LAM, t->name, ann, body);
}

static const Core *infer_lam(Checker *c, const Term *t, const Value **type) {
  uint64_t level = 0;
  const Value *dom;
  const Value *bt = NULL;
  const Core *body;
  const Core *quoted;
  const Core *ann;
  if (t->left == NULL)
    return nul(FAIL(c, "TYPE_INFER", "fun %s => ... needs a binder type here", t->name));
  if (is_interval(c, t->left))
    return infer_plam(c, t, type);
  ann = check_type(c, t->left, &level);
  dom = here(c, ann);
  if (!push(c, t->name, dom))
    return NULL;
  body = infer(c, t->right, &bt);
  quoted = body == NULL ? NULL : quote_value(c->m, c->level, bt);
  pop(c);
  *type = val_closure(c->m, VAL_PI, t->name, dom, c->env, quoted);
  return core_bind(c, CORE_LAM, t->name, ann, body);
}

/* (x : A) -> B and Sigma (x : A) B. */
static const Core *elab_binder(Checker *c, const Term *t, CoreKind kind, const Value *hint, const Value **type) {
  uint64_t la = 0;
  uint64_t lb = 0;
  const Core *a = check_type(c, t->left, &la);
  const Core *b;
  if (a == NULL || !push(c, t->name, here(c, a)))
    return NULL;
  b = check_type(c, t->right, &lb);
  pop(c);
  *type = val_univ(c->m, la > lb ? la : lb);
  return finish(c, core_bind(c, kind, t->name, a, b), hint, type);
}

/* p @ r: p : PathP L a b and r : I give L[r]. The core keeps a and b. */
static const Core *elab_papp(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Value *pt = NULL;
  const Core *p = infer(c, t->left, &pt);
  const Core *r;
  if (p == NULL)
    return NULL;
  if (pt == NULL || pt->kind != VAL_PATHP)
    return nul(FAIL(c, "TYPE_MISMATCH", "@ needs a path of type PathP L a b, found a term of type %s", show(c, pt)));
  r = check(c, t->right, interval_type(c));
  *type = r == NULL ? NULL : closure_apply(c->m, pt, here(c, r));
  return finish(c, core_ends(c, CORE_PAPP, NULL, p, r, quote_value(c->m, c->level, pt->args[0]), quote_value(c->m, c->level, pt->args[1])), hint, type);
}

/* ~r, r /\ s and r \/ s: the operands and the result are in I. */
static const Core *elab_ival(Checker *c, const Term *t, CoreKind kind, const Value *hint, const Value **type) {
  const Value *iv = interval_type(c);
  const Core *a = check(c, t->left, iv);
  const Core *b = kind == CORE_INEG || a == NULL ? NULL : check(c, t->right, iv);
  *type = iv;
  return finish(c, core_iop(c, kind, a, b), hint, type);
}

/* The append defs of `c ++ d` (S6 u7, USER ruling Q-S6-36 (a)), in the
   order of the test. */
static const char *const APPEND_DEFS[] = {"traceAppend", "chainAppend"};

/* A copy of AT with the kind KIND, the name NAME and the parts LEFT and
   RIGHT. The line and the column of AT stay. */
static Term *append_term(Checker *c, const Term *at, TermKind kind, const char *name, const Term *left, const Term *right) {
  Term *t = arena_alloc(c->m->arena, sizeof *t);
  if (t == NULL) {
    FAIL(c, "OOM", "out of memory");
    return NULL;
  }
  *t = *at;
  t->kind = kind;
  t->name = name;
  t->left = left;
  t->right = right;
  return t;
}

/* `c ++ d` (S6 u7, USER ruling Q-S6-36 (a)): the type of c selects the
   def. A def of APPEND_DEFS applies when the domain of its type converts
   with the type of c: a Trace gives traceAppend and a Blockchain gives
   chainAppend. The core gets the app `def c d`, so eval, ir and wasm do
   not change. When no def applies, the result is REFUSE_APPEND. */
static const Core *elab_append(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Value *left = NULL;
  const char *def = NULL;
  const Term *fn;
  const Term *head;
  const Term *app;
  uint32_t i;
  if (infer(c, t->left, &left) == NULL || left == NULL)
    return NULL;
  for (i = 0; def == NULL && i < sizeof APPEND_DEFS / sizeof APPEND_DEFS[0]; i++) {
    const Value *ft = NULL;
    const Term *name = append_term(c, t, TERM_VAR, APPEND_DEFS[i], NULL, NULL);
    if (name == NULL)
      return NULL;
    if (try_infer(c, name, &ft) != NULL && ft != NULL && ft->kind == VAL_PI && conv_values(c->m, c->level, ft->dom, left))
      def = APPEND_DEFS[i];
  }
  if (def == NULL)
    return nul(FAIL(c, "REFUSE_APPEND", "the left side of ++ is not a Trace or a Blockchain, so no append def applies (S6 u7)"));
  fn = append_term(c, t, TERM_VAR, def, NULL, NULL);
  head = fn == NULL ? NULL : append_term(c, t, TERM_APP, NULL, fn, t->left);
  app = head == NULL ? NULL : append_term(c, t, TERM_APP, NULL, head, t->right);
  return app == NULL ? NULL : elab(c, app, hint, type);
}

static const Core *elab_inner(Checker *c, const Term *t, const Value *hint, const Value **type) {
  switch (t->kind) {
  case TERM_VAR:
  case TERM_APP:
    return elab_spine(c, t, hint, type);
  case TERM_NAT:
    /* An Amount literal (S2, USER ruling Q-S2-2 (a)): a numeral is a
       guest literal when the wanted type is Amount. The lexer refuses
       a numeral above 2^64 - 1. */
    if (val_is(hint, OP_AMOUNT)) {
      *type = hint;
      return core_leaf(c, CORE_NAT, t->nat);
    }
    if (!literal_ok(c, "a Nat literal"))
      return NULL;
    if (val_is(hint, OP_FIN) && hint->args[0]->kind == VAL_NAT) {
      if (t->nat >= hint->args[0]->nat)
        return nul(FAIL(c, "FIN_RANGE", "the literal %llu is not below %llu, so it is not a value of Fin %llu", (unsigned long long)t->nat, (unsigned long long)hint->args[0]->nat, (unsigned long long)hint->args[0]->nat));
      *type = hint;
      return core_leaf(c, CORE_NAT, t->nat);
    }
    /* REFUSE_PARTIAL site 3 (S3): a literal other than 0
       checks as a NonZero Nat. */
    if (val_is(hint, OP_NONZERO) && val_is(hint->args[0], OP_NAT)) {
      if (t->nat == 0u)
        return nul(FAIL(c, "REFUSE_PARTIAL", "the literal 0 is not a value of NonZero Nat: use nonZero, which gives an Option"));
      *type = hint;
      return core_leaf(c, CORE_NAT, t->nat);
    }
    *type = nat_type(c);
    return finish(c, core_leaf(c, CORE_NAT, t->nat), hint, type);
  case TERM_LAM:
    return hint != NULL ? check_lam(c, t, hint, type) : infer_lam(c, t, type);
  case TERM_PI:
    return elab_binder(c, t, CORE_PI, hint, type);
  case TERM_SIGMA:
    return elab_binder(c, t, CORE_SIGMA, hint, type);
  case TERM_UNIV:
    if (t->nat >= UNIVERSE_MAX)
      return nul(FAIL(c, "TYPE_UNIVERSE", "Type %llu is above the largest universe Type %u", (unsigned long long)t->nat, UNIVERSE_MAX - 1u));
    *type = val_univ(c->m, t->nat + 1u);
    return finish(c, core_leaf(c, CORE_UNIV, t->nat), hint, type);
  case TERM_PAPP:
    return elab_papp(c, t, hint, type);
  case TERM_INEG:
    return elab_ival(c, t, CORE_INEG, hint, type);
  case TERM_IMEET:
    return elab_ival(c, t, CORE_IMEET, hint, type);
  case TERM_IJOIN:
    return elab_ival(c, t, CORE_IJOIN, hint, type);
  case TERM_APPEND:
    return elab_append(c, t, hint, type);
  case TERM_SYSTEM:
  case TERM_BRANCH:
    return nul(FAIL(c, "TYPE_MISMATCH", "a system [ phi -> t, ... ] is only the tube of hcomp, fun (i : I) => [ ... ]"));
  }
  return NULL;
}

static const Core *elab(Checker *c, const Term *t, const Value *hint, const Value **type) {
  const Core *k;
  if (c->depth >= CHECK_DEPTH_LIMIT)
    return nul(FAIL(c, "CHECK_DEPTH", "the term is nested deeper than %u levels", CHECK_DEPTH_LIMIT));
  c->depth++;
  k = elab_inner(c, t, hint, type);
  c->depth--;
  return k;
}

/* NULL when NAME is free, else the reason it is taken (rule R4). */
static const char *name_owner(const Checker *c, const char *name) {
  const Machine *m = c->m;
  uint32_t i;
  uint32_t j;
  for (i = 0; i < sizeof RESERVED / sizeof RESERVED[0]; i++) {
    if (strcmp(RESERVED[i], name) == 0)
      return "a reserved name";
  }
  for (i = 0; i < BUILTIN_COUNT; i++) {
    if (strcmp(BUILTINS[i].name, name) == 0)
      return "a core name";
  }
  for (i = 0; i < m->family_count; i++) {
    if (strcmp(m->families[i].name, name) == 0)
      return "a domain family";
  }
  for (i = 0; i < m->ctor_count; i++) {
    for (j = 0; j < m->ctors[i].field_count; j++) {
      if (strcmp(m->ctors[i].fields[j].name, name) == 0)
        return "a domain field";
    }
    if (m->ctors[i].name != NULL && strcmp(m->ctors[i].name, name) == 0)
      return "a domain constructor";
  }
  for (i = 0; i < m->space_count; i++) {
    if (strcmp(m->spaces[i].name, name) == 0)
      return "a key space";
  }
  i = find_def(m, name);
  if (i == NO_DEF)
    return NULL;
  return m->defs[i].origin != ORIGIN_PROGRAM ? "a domain definition" : "already defined";
}

static int name_free(Checker *c, const char *name) {
  const char *why;
  const DroppedName *x = dropped_name(name);
  if (x != NULL)
    return FAIL(c, "REFUSE_NOT_IN_DESIGN", DROPPED_HINT, name, x->row, x->why);
  if (time_word(name))
    return FAIL(c, "REFUSE_TIME", TIME_HINT, name);
  why = name_owner(c, name);
  return why == NULL ? 1 : FAIL(c, "REFUSE_NAME", "%s is %s (rule R4)", name, why);
}

/* T is a sort of the block of FAM at the parameter variables of FAM
   `F p1 .. pn`, then any index arguments (S6), in the context of the
   parameters and SHIFT earlier fields (S4 items 9 and 13). */
static int own_family(const Machine *m, uint32_t fam, const Core *t, uint32_t shift) {
  const FamilyInfo *f = &m->families[fam];
  uint32_t p = f->param_count;
  uint32_t k;
  if (t->kind != CORE_OP || t->op != OP_FAMILY || t->inst < f->block_first || t->inst - f->block_first >= f->block_count)
    return 0;
  if (m->families[t->inst].param_count != p || t->argc != p + m->families[t->inst].index_count)
    return 0;
  for (k = 0; k < p; k++)
    if (t->args[k]->kind != CORE_VAR || t->args[k]->index != p - 1u - k + shift)
      return 0;
  return 1;
}

/* A family with a type parameter is a type constructor, so it must be a
   cell signature (S3, rule R1): only type parameters, no and block, each
   type parameter the one field of exactly one generator constructor, and
   every other point field closed data, the family at its own parameters
   or a path in it. REFUSE_CELL comes before DOMAIN_FAMILY. */
static int cell_type_argument(const Core *t) {
  while (t->kind == CORE_PI)
    t = t->b;
  return t->kind == CORE_UNIV;
}

static int has_type_param(const FamilyInfo *f) {
  uint32_t k;
  for (k = 0; k < f->param_count; k++)
    if (cell_type_argument(f->param_types[k]))
      return 1;
  return 0;
}

/* The type parameter that T is, in the context of the parameters and
   EARLIER fields, or the parameter count when T is not one. */
static uint32_t cell_param(const FamilyInfo *f, const Core *t, uint32_t earlier) {
  uint32_t p = f->param_count;
  uint32_t k = t->kind == CORE_VAR && t->index >= earlier && t->index - earlier < p ? p - 1u - (t->index - earlier) : p;
  return k < p && f->param_types[k]->kind == CORE_UNIV ? k : p;
}

static int cell_header(Checker *c, const Decl *d, uint32_t first, uint32_t count) {
  uint32_t s, k;
  for (s = 0; s < count; s++) {
    const FamilyInfo *f = &c->m->families[first + s];
    for (k = 0; k < f->index_count; k++)
      if (cell_type_argument(f->index_types[k]))
        return FAIL(c, "REFUSE_CELL", "%s has a type index; a cell signature binds its type arguments as uniform parameters (rule R1)", f->name);
    for (k = 0; has_type_param(f) && k < f->param_count; k++) {
      if (count > 1u && f->param_types[k]->kind == CORE_UNIV)
        return FAIL(c, "REFUSE_CELL", "%s has the type parameter %s in an and block; a type constructor is one cell signature (rule R1)", f->name, d[s].params[k].name);
      if (f->param_types[k]->kind != CORE_UNIV)
        return FAIL(c, "REFUSE_CELL", "%s has a type argument and the parameter %s is not a universe; a cell signature has only type parameters (rule R1)", f->name, d[s].params[k].name);
    }
  }
  return 1;
}

/* Closed operation labels cannot depend on a type parameter or an earlier
   field. Binders inside the label type still bind their own variables. */
static int cell_closed(const Core *t, uint32_t depth) {
  uint32_t i;
  int binder;
  if (t == NULL)
    return 1;
  if (t->kind == CORE_VAR)
    return t->index < depth;
  binder = t->kind == CORE_PI || t->kind == CORE_SIGMA || t->kind == CORE_LAM || t->kind == CORE_PLAM || t->kind == CORE_PATHP;
  if (!cell_closed(t->a, depth) || !cell_closed(t->b, depth + (uint32_t)binder))
    return 0;
  for (i = 0; i < t->argc; i++)
    if (!cell_closed(t->args[i], depth))
      return 0;
  return 1;
}

static int cell_field(Checker *c, uint32_t fam, const FieldInfo *out, uint32_t earlier, size_t field_count) {
  const FamilyInfo *f = &c->m->families[fam];
  const Core *t = out->type;
  if (cell_param(f, t, earlier) < f->param_count)
    return field_count == 1u ? 1 : FAIL(c, "REFUSE_CELL", "%s is not a cell signature: the field %s has a type parameter as its type, so it must be the one field of its constructor (rule R1)", f->name, out->name);
  if (own_family(c->m, fam, t, earlier) || (t->kind == CORE_PATHP && own_family(c->m, fam, t->b, earlier + 1u)))
    return 1;
  if (c->self_uses == 0u && cell_closed(t, 0u))
    return 1;
  return FAIL(c, "REFUSE_CELL", "%s is not a cell signature: the field %s must be a type parameter, closed data, %s at its own parameters or a path in %s (rule R1)", f->name, out->name, f->name, f->name);
}

/* Each type parameter has exactly one generator (S3, open point QA1:
   two generators for one parameter are refused). */
static int cell_generators(Checker *c, const Decl *d, uint32_t fam) {
  const Machine *m = c->m;
  const FamilyInfo *f = &m->families[fam];
  uint32_t k, i;
  for (k = 0; k < f->param_count; k++) {
    uint32_t gens = 0;
    for (i = 0; i < f->ctor_count; i++)
      gens += m->ctors[f->first_ctor + i].field_count == 1u && cell_param(f, m->ctors[f->first_ctor + i].fields[0].type, 0u) == k;
    if (gens == 0u)
      return FAIL(c, "REFUSE_CELL", "%s is not a cell signature: the type parameter %s occurs in no constructor (rule R1)", f->name, d->params[k].name);
    if (gens > 1u)
      return FAIL(c, "REFUSE_CELL", "%s is not a cell signature: the type parameter %s has %u generators (rule R1)", f->name, d->params[k].name, (unsigned)gens);
  }
  return 1;
}

/* A recursive field must be the whole field type, the family at its own
   parameters. The EARLIER point fields are locals (S4 item 13). */
static int check_field(Checker *c, uint32_t fam, const Field *field, FieldInfo *out, uint32_t earlier, size_t field_count) {
  uint64_t level = 0;
  const Core *t;
  if (!name_free(c, field->name))
    return 0;
  c->self_uses = 0;
  c->field_base = c->level - earlier;
  c->field_top = c->level;
  c->field_dep = 0;
  c->field_rec = 0;
  t = check_type(c, field->type, &level);
  c->field_top = c->field_base;
  if (t == NULL)
    return 0;
  if (level > c->m->families[fam].universe)
    c->m->families[fam].universe = level;
  out->name = field->name;
  out->type = t;
  /* A path type over earlier recursive fields names the family, but it is
     a path field, not a recursive field (S4 item 14). */
  out->recursive = c->self_uses > 0u && !(t->kind == CORE_PATHP && c->field_rec);
  out->dependent = c->field_dep;
  out->over_recursive = c->field_rec;
  out->history = field->history;
  if (has_type_param(&c->m->families[fam]) && !cell_field(c, fam, out, earlier, field_count))
    return 0;
  if (out->recursive && !own_family(c->m, fam, t, earlier))
    return FAIL(c, "DOMAIN_FAMILY", "the recursive field %s must have the type %s at its own parameters", field->name, c->m->families[fam].name);
  return 1;
}

/* The field EARLIER of FIELDS is a path field when it uses an earlier
   recursive field and its type is `Path F x y`: F the family at its own
   parameters, x and y earlier recursive fields (S4 item 14). An other
   field over a recursive field has no fold case type. */
static void path_field(const Machine *m, uint32_t fam, FieldInfo *fields, uint32_t earlier) {
  FieldInfo *f = &fields[earlier];
  const Core *t = f->type;
  int side;
  f->path = f->over_recursive && t->kind == CORE_PATHP && own_family(m, fam, t->b, earlier + 1u);
  for (side = 0; side < 2; side++) {
    const Core *e = f->path ? t->args[side] : NULL;
    f->path = f->path && e != NULL && e->kind == CORE_VAR && e->index < earlier && fields[earlier - 1u - e->index].recursive;
    f->ends[side] = f->path ? earlier - 1u - e->index : 0u;
  }
}

/* A term that the checker makes, at the place of CTOR. */
static Term *made_term(Checker *c, const Ctor *ctor, TermKind kind, const char *name, const Term *left, const Term *right) {
  Term *t = arena_alloc(c->m->arena, sizeof *t);
  if (t == NULL) {
    FAIL(c, "OOM", "out of memory");
    return NULL;
  }
  t->kind = kind;
  t->line = ctor->line;
  t->col = ctor->col;
  t->name = name;
  t->nat = 0;
  t->left = left;
  t->right = right;
  return t;
}

/* COVER \/ (~NAME \/ NAME), or ~NAME \/ NAME when COVER is NULL. */
static const Term *cover_term(Checker *c, const Ctor *ctor, const Term *cover, const char *name) {
  const Term *v = made_term(c, ctor, TERM_VAR, name, NULL, NULL);
  const Term *neg = v == NULL ? NULL : made_term(c, ctor, TERM_INEG, NULL, v, NULL);
  const Term *ends = neg == NULL ? NULL : made_term(c, ctor, TERM_IJOIN, NULL, neg, v);
  return cover == NULL || ends == NULL ? ends : made_term(c, ctor, TERM_IJOIN, NULL, cover, ends);
}

/* A branch of a path constructor of the indexed sort FAM failed (S6). A
   body of the type FAM at another index is HIT_INDEX (the gate row "a
   wrong index in a path constructor"), not the TYPE_MISMATCH of the
   branch check. */
static int branch_index(Checker *c, uint32_t fam, const Branch *b) {
  Diag saved = *c->m->diag;
  const Value *t = NULL;
  if (c->m->families[fam].index_count == 0u || saved.code == NULL || strcmp(saved.code, "TYPE_MISMATCH") != 0 || b->term == NULL || b->term->right == NULL)
    return 0;
  c->m->diag->set = 0;
  if (infer(c, b->term->right, &t) != NULL && val_is(t, OP_FAMILY) && t->inst == fam) {
    *c->m->diag = saved;
    c->m->diag->set = 0;
    return FAIL(c, "HIT_INDEX", "a boundary term of a path constructor of %s has the type %s, the family at another index", c->m->families[fam].name, show(c, t));
  }
  *c->m->diag = saved;
  return 0;
}

/* The boundary of CTOR under its fields: the first POINTS fields of CTOR
   (with FIELDS their checked types) and then its interval fields are
   locals. The family parameters are already locals (check_family). Each
   branch has the family at the parameters and RESULT, the result indices
   of CTOR (S6), NULL for a uniform family. */
static const Core *boundary_core(Checker *c, uint32_t fam, const Ctor *ctor, const FieldInfo *fields, size_t points, const Core *const *result) {
  Machine *m = c->m;
  uint32_t p = m->families[fam].param_count;
  uint32_t q = result == NULL ? p : p + m->families[fam].index_count;
  const Value **params = arena_alloc(m->arena, ((size_t)q + 1u) * sizeof *params);
  Term *tube = arena_alloc(m->arena, sizeof *tube);
  const Term *cover = NULL;
  const Core *phi;
  const Core *a;
  Branch *bs;
  uint32_t n = 0;
  uint32_t i;
  size_t j;
  if (params == NULL || tube == NULL)
    return nul(FAIL(c, "OOM", "out of memory"));
  for (i = 0; i < p; i++)
    params[i] = val_var(m, c->level - p + i);
  /* Field j is over the earlier fields: evaluate it after they are pushed. */
  for (j = 0; j < points; j++)
    if (!push(c, fields[j].name, here(c, fields[j].type)))
      return NULL;
  /* The result indices at the parameters and the point fields (S6). */
  for (i = p; i < q; i++) {
    params[i] = here(c, result[i - p]);
    if (params[i] == NULL)
      return NULL;
  }
  for (j = points; j < ctor->field_count; j++) {
    cover = cover_term(c, ctor, cover, ctor->fields[j].name);
    if (cover == NULL || !push_interval(c, ctor->fields[j].name))
      return NULL;
  }
  phi = check(c, cover, interval_type(c));
  a = quote_value(m, c->level, val_op(m, VAL_OP, OP_FAMILY, fam, 0, params, q));
  if (phi == NULL || a == NULL)
    return NULL;
  tube->kind = TERM_LAM;
  tube->line = ctor->line;
  tube->col = ctor->col;
  tube->name = NULL;
  tube->nat = 0;
  tube->left = NULL;
  tube->right = ctor->boundary;
  bs = system_branches(c, tube, here(c, phi), &n);
  if (bs == NULL)
    return NULL;
  for (i = 0; i < n; i++) {
    bs[i].body = hcomp_branch(c, NULL, a, &bs[i]);
    if (bs[i].body == NULL)
      return nul(branch_index(c, fam, &bs[i]));
  }
  if (!system_overlaps(c, "_", bs, n))
    return NULL;
  return system_core(c, "_", bs, n);
}

/* The boundary `[ k1 -> t1, ... ]` of a path constructor (S4 R1 (a)),
   checked as the tube of an hcomp at the family: each branch has the
   family type at the parameters, the keys cover ~i \/ i (and ~j \/ j)
   (SYSTEM_COVER) and two branches agree where both keys hold
   (SYSTEM_OVERLAP). The core is OP_SYSTEM, each body under a path binder
   that no term can use, as an hcomp tube. The context comes back as it
   was. */
static const Core *check_boundary(Checker *c, uint32_t fam, const Ctor *ctor, const FieldInfo *fields, size_t points, const Core *const *result) {
  const Scope *scope = c->scope;
  const Env *env = c->env;
  uint32_t level = c->level;
  const Core *sys = boundary_core(c, fam, ctor, fields, points, result);
  c->scope = scope;
  c->env = env;
  c->level = level;
  return sys;
}

/* The result `: F params indices` of CTOR under its POINTS point fields
   (S6). A constructor of an indexed sort states it: its head is the sort
   at its own parameters, and its index arguments check against the index
   telescope. A constructor of a uniform sort can state the sort at its
   parameters. RESULT gets the index cores, or NULL. */
static int ctor_result(Checker *c, uint32_t fam, const Ctor *ctor, uint32_t points, const Core *const **result) {
  const FamilyInfo *f = &c->m->families[fam];
  uint64_t level = 0;
  const Core *t;
  *result = NULL;
  if (ctor->result == NULL)
    return f->index_count == 0u ? 1 : FAIL(c, "HIT_INDEX", "the constructor %s of the indexed family %s needs a result `: %s ...` after its fields", ctor->name, f->name, f->name);
  t = check_type(c, ctor->result, &level);
  if (t == NULL)
    return 0;
  if (!own_family(c->m, fam, t, points) || t->inst != fam)
    return FAIL(c, "HIT_INDEX", "the result of %s must be %s at its own parameters", ctor->name, f->name);
  *result = f->index_count == 0u ? NULL : t->args + f->param_count;
  return 1;
}

/* A constructor takes point fields, then (a path constructor) 1 or 2
   interval fields `(i : I)` and a boundary. It fills the reserved slot
   SLOT (S6). */
static int check_ctor(Checker *c, uint32_t fam, const Ctor *ctor, uint32_t slot) {
  Machine *m = c->m;
  FieldInfo *fields = arena_alloc(m->arena, (ctor->field_count + 1u) * sizeof *fields);
  CtorInfo *ci = &m->ctors[slot];
  const Core *const *result = NULL;
  const Scope *scope = c->scope;
  const Env *env = c->env;
  uint32_t level = c->level;
  const Core *boundary = NULL;
  size_t points = 0;
  size_t j;
  if (fields == NULL)
    return FAIL(c, "OOM", "out of memory");
  if (!name_free(c, ctor->name))
    return 0;
  for (j = 0; j < ctor->field_count; j++) {
    int interval = is_interval(c, ctor->fields[j].type);
    if (strcmp(ctor->fields[j].name, ctor->name) == 0)
      return FAIL(c, "REFUSE_NAME", "%s is this domain constructor (rule R4)", ctor->name);
    for (size_t k = 0; k < j; k++)
      if (strcmp(ctor->fields[j].name, ctor->fields[k].name) == 0)
        return FAIL(c, "REFUSE_NAME", "%s is already a field of this domain constructor (rule R4)", ctor->fields[j].name);
    if (!interval && points < j)
      return FAIL(c, "HIT_BOUNDARY", "the point field %s of %s must come before the interval fields", ctor->fields[j].name, ctor->name);
    if (interval && !name_free(c, ctor->fields[j].name))
      return 0;
    if (!interval && !check_field(c, fam, &ctor->fields[j], &fields[j], (uint32_t)points, ctor->field_count))
      return 0;
    if (!interval) {
      path_field(m, fam, fields, (uint32_t)points);
      if (c->self_uses > 0u && !fields[j].recursive && !fields[j].path)
        return FAIL(c, "DOMAIN_FAMILY", "the field %s must be a direct recursive field or a path between earlier recursive fields", fields[j].name);
    }
    /* A later field type can use this field (S4 item 13). */
    if (!interval && !push(c, fields[j].name, here(c, fields[j].type)))
      return 0;
    points += !interval;
  }
  if (!ctor_result(c, fam, ctor, (uint32_t)points, &result))
    return 0;
  c->scope = scope;
  c->env = env;
  c->level = level;
  if (ctor->field_count - points > 2u)
    return FAIL(c, "HIT_BOUNDARY", "%s has %u interval fields; a path constructor has 1 or 2", ctor->name, (unsigned)(ctor->field_count - points));
  if (points < ctor->field_count && ctor->boundary == NULL)
    return FAIL(c, "HIT_BOUNDARY", "the path constructor %s needs a boundary [ ~i -> t0, i -> t1 ] after its interval fields", ctor->name);
  /* A boundary with no interval field (a point constructor or a state)
     gives DOMAIN_FAMILY, as the USER guard of cdfc751 did. */
  if (points == ctor->field_count && ctor->boundary != NULL)
    return FAIL(c, "DOMAIN_FAMILY", "%s has a boundary but no interval field; only a path constructor has a boundary", ctor->name);
  if (ctor->boundary != NULL) {
    boundary = check_boundary(c, fam, ctor, fields, points, result);
    if (boundary == NULL)
      return 0;
  }
  ci->name = ctor->name;
  ci->family = fam;
  ci->fields = fields;
  ci->field_count = (uint32_t)points;
  ci->interval_count = (uint32_t)(ctor->field_count - points);
  ci->boundary = boundary;
  ci->result = result;
  return 1;
}

static int kernel_sig(Checker *c, const Decl *d);

/* T has a free variable NAME. A local binder can shadow a block sort. */
static int names_var(const Term *t, const char *name) {
  if (t == NULL)
    return 0;
  if (t->kind == TERM_VAR && t->name != NULL && strcmp(t->name, name) == 0)
    return 1;
  if (names_var(t->left, name))
    return 1;
  if ((t->kind == TERM_PI || t->kind == TERM_LAM || t->kind == TERM_SIGMA) && t->name != NULL && strcmp(t->name, name) == 0)
    return 0;
  return names_var(t->right, name);
}

/* The header of the sort S of the block FIRST of COUNT sorts names no
   sort from S on (S6): its parameters and its index telescope can name
   only the earlier sorts (BLOCK_ORDER). */
static int header_order(Checker *c, const Decl *first, uint32_t s, uint32_t count) {
  const Decl *d = &first[s];
  uint32_t t;
  size_t i;
  for (t = s; t < count; t++) {
    int named = 0;
    for (i = 0; i < d->param_count; i++) {
      named |= names_var(d->params[i].type, first[t].name);
      if (strcmp(d->params[i].name, first[t].name) == 0)
        break;
    }
    if (i == d->param_count)
      named |= names_var(d->index, first[t].name);
    if (named)
      return FAIL(c, "BLOCK_ORDER", "the header of %s names the block sort %s; a header can name only the earlier sorts of its block", d->name, first[t].name);
  }
  return 1;
}

/* The header of the block sort D as the family FAM of the block FIRST of
   COUNT sorts (S6): the parameters, then the index telescope `T1 -> ...
   -> Type 0`, in an empty context. Prop and SProp are not types there
   (NAME_UNKNOWN, rule R4). The constructor slots of D are reserved here,
   so the constructors of a sort stay contiguous. */
static int check_header(Checker *c, const Decl *d, uint32_t fam, uint32_t first, uint32_t count, uint64_t universe) {
  Machine *m = c->m;
  FamilyInfo *f = &m->families[fam];
  const Core **params = arena_alloc(m->arena, (d->param_count + 1u) * sizeof *params);
  const Core **indices;
  const Term *t;
  uint32_t n = 0;
  size_t i;
  for (t = d->index; t != NULL && t->kind == TERM_PI; t = t->right)
    n++;
  indices = arena_alloc(m->arena, ((size_t)n + 1u) * sizeof *indices);
  if (params == NULL || indices == NULL)
    return FAIL(c, "OOM", "out of memory");
  c->scope = NULL;
  c->env = NULL;
  c->level = 0;
  for (i = 0; i < d->param_count; i++) {
    uint64_t level = 0;
    params[i] = check_type(c, d->params[i].type, &level);
    /* Expose universe and higher-kind aliases before the cell check. */
    if (params[i] != NULL)
      params[i] = quote_value(m, c->level, here(c, params[i]));
    if (params[i] == NULL || !push(c, d->params[i].name, here(c, params[i])))
      return 0;
  }
  for (t = d->index, i = 0; t != NULL && t->kind == TERM_PI; t = t->right, i++) {
    uint64_t level = 0;
    indices[i] = check_type(c, t->left, &level);
    if (indices[i] != NULL)
      indices[i] = quote_value(m, c->level, here(c, indices[i]));
    if (indices[i] == NULL || !push(c, t->name == NULL ? "_" : t->name, here(c, indices[i])))
      return 0;
  }
  if (t != NULL && (t->kind != TERM_UNIV || t->nat != 0u))
    return FAIL(c, "TYPE_MISMATCH", "the index telescope of %s must end in Type 0", d->name);
  f->name = d->name;
  f->param_types = params;
  f->param_count = (uint32_t)d->param_count;
  f->index_types = indices;
  f->index_count = n;
  f->block_first = first;
  f->block_count = count;
  f->first_ctor = m->ctor_count;
  f->ctor_count = (uint32_t)d->ctor_count;
  f->universe = universe;
  f->origin = d->origin;
  for (i = 0; i < d->ctor_count; i++) {
    memset(&m->ctors[m->ctor_count + i], 0, sizeof m->ctors[0]);
    m->ctors[m->ctor_count + i].family = fam;
  }
  m->ctor_count += (uint32_t)d->ctor_count;
  m->family_count++;
  return 1;
}

/* A block of sorts D[0 .. block_count) (S6); a family outside a block is a
   block of one. All headers bind first, then the point constructors of
   all sorts, then the path constructors of all sorts, so a boundary can
   name a point constructor of a later sort. The sorts of the block are in
   scope in the fields, so a field can be recursive. */
static int check_family(Checker *c, const Decl *d) {
  Machine *m = c->m;
  uint32_t first = m->family_count;
  uint32_t count = d->block_count > 0u ? (uint32_t)d->block_count : 1u;
  uint32_t first_ctor = m->ctor_count;
  uint64_t *universes = arena_alloc(m->arena, (size_t)count * sizeof *universes);
  uint32_t s;
  int pass;
  if (universes == NULL)
    return FAIL(c, "OOM", "out of memory");
  memset(universes, 0, (size_t)count * sizeof *universes);
  c->self = first;
  c->self_count = count;
  /* A later sort can raise the universe of an earlier sort. Recheck
     headers and constructors until these monotone universe bounds settle,
     so no core retains an elaboration made at a provisional lower level. */
  for (;;) {
    int changed = 0;
    m->family_count = first;
    m->ctor_count = first_ctor;
    for (s = 0; s < count; s++) {
      m->def = d[s].name;
      if (s > 0u && (!kernel_sig(c, &d[s]) || !name_free(c, d[s].name)))
        return 0;
      if (!header_order(c, d, s, count) || !check_header(c, &d[s], first + s, first, count, universes[s]))
        return 0;
    }
    if (!cell_header(c, d, first, count))
      return 0;
    for (pass = 0; pass < 2; pass++) {
      for (s = 0; s < count; s++) {
        const FamilyInfo *f = &m->families[first + s];
        size_t i;
        m->def = d[s].name;
        c->scope = NULL;
        c->env = NULL;
        c->level = 0;
        for (i = 0; i < d[s].param_count; i++)
          if (!push(c, d[s].params[i].name, here(c, f->param_types[i])))
            return 0;
        for (i = 0; i < d[s].ctor_count; i++)
          if ((d[s].ctors[i].boundary != NULL) == (pass == 1) && !check_ctor(c, first + s, &d[s].ctors[i], f->first_ctor + (uint32_t)i))
            return 0;
      }
    }
    for (s = 0; s < count; s++) {
      changed |= universes[s] != m->families[first + s].universe;
      universes[s] = m->families[first + s].universe;
    }
    if (!changed)
      break;
  }
  if (count == 1u && has_type_param(&m->families[first]) && !cell_generators(c, d, first))
    return 0;
  /* A sealed family is a cell monad (S5, rule O7). */
  if (d->is_sealed && (count != 1u || !has_type_param(&m->families[first])))
    return FAIL(c, "REFUSE_CELL", "%s is sealed but is not a cell monad: a sealed family has a type parameter and no and block (rule O7)", d->name);
  for (s = 0; s < count; s++)
    m->families[first + s].sealed = d[s].is_sealed;
  return 1;
}

/* A bind variable of rule D-9 (S3): in
   bind ADD (fun v => b), the variable v has the de Bruijn level LEVEL in b. */
typedef struct HistBind {
  uint32_t level;
  const Core *add;
  const struct HistBind *next;
} HistBind;

static const HistBind *hist_bind(const HistBind *b, uint32_t level) {
  return b == NULL || b->level == level ? b : hist_bind(b->next, level);
}

/* Rule D-9 (slice K3c). The argument A of the history field K of the state
   constructor CTOR is `F t`, `natAdd (F t) e`, or the variable v of
   bind (natAdd (F t) e) (fun v => ...) (S3), with F the
   projection of the field. natAdd gives an Option Nat (N1), so a Nat field
   takes the bind form. DEPTH is the count of binders above A; BINDS lists
   the bind variables. */
static int history_arg_ok(uint32_t ctor, uint32_t k, const Core *a, uint32_t depth, const HistBind *binds) {
  const Core *x = a->kind == CORE_OP && a->op == OP_NAT_ADD && a->argc == 2u ? a->args[0] : a;
  const HistBind *b = a->kind == CORE_VAR && a->index < depth ? hist_bind(binds, depth - 1u - a->index) : NULL;
  if (b != NULL)
    return history_arg_ok(ctor, k, b->add, 0, NULL);
  return x->kind == CORE_OP && x->op == OP_PROJ && x->inst == ctor && x->field == k;
}

static int is_family(const Value *t, uint32_t family);

/* Rule D-9 (USER ruling A). The rule does not check the body of init or of
   a definition with the type State after normalization. */
static int history_root(const Machine *m, uint32_t j) {
  return strcmp(m->defs[j].name, "init") == 0 || is_family(m->defs[j].type, m->state_family);
}

static int has_history(const Machine *m) {
  const CtorInfo *ci;
  uint32_t i;
  if (!m->has_state)
    return 0;
  ci = &m->ctors[m->families[m->state_family].first_ctor];
  for (i = 0; i < ci->field_count; i++) {
    if (ci->fields[i].history)
      return 1;
  }
  return 0;
}

/* 1 if the family State occurs in the type value V (USER ruling A). The
   codomain of a Pi or a Sigma opens at a fresh level, as conv_values does.
   A variable can stand for State, including the payload type of an
   existential package. A Lam, a stuck operation or a value that does not
   open also gives 1. */
static int mentions_state(Machine *m, uint32_t level, const Value *v) {
  uint32_t i;
  if (v == NULL)
    return 1;
  switch (v->kind) {
  case VAL_NAT:
  case VAL_UNIV:
    return 0;
  case VAL_PI:
  case VAL_SIGMA:
    return mentions_state(m, level, v->dom) || mentions_state(m, level + 1u, closure_apply(m, v, val_var(m, level)));
  case VAL_APP:
  case VAL_PAPP:
    return mentions_state(m, level, v->dom) || mentions_state(m, level, v->arg);
  case VAL_PLAM:
    return mentions_state(m, level + 1u, closure_apply(m, v, val_ivar(m, level)));
  case VAL_PATHP:
    return mentions_state(m, level, v->args[0]) || mentions_state(m, level, v->args[1]) || mentions_state(m, level + 1u, closure_apply(m, v, val_ivar(m, level)));
  case VAL_IVAL:
    return 0;
  case VAL_LAM:
  case VAL_STUCK:
  case VAL_VAR:
    return 1;
  case VAL_OP:
    break;
  }
  if (is_family(v, m->state_family))
    return 1;
  for (i = 0; i < v->argc; i++) {
    if (mentions_state(m, level, v->args[i]))
      return 1;
  }
  return 0;
}

/* Rule D-9 (slice K3c) on the core term T of a definition. The names are
   resolved, so a binder with the name of a field is a local and not the
   field. Each use of the state constructor has all of its arguments and
   keeps or adds to each history field. TYPED is 1 when State occurs in the
   type of the definition: then T cannot refer to a definition that the rule
   does not check (history_root). DEPTH and BINDS are as history_arg_ok
   (S3); the type of a path type opens with no bind variables. */
static int history_ok(Checker *c, const Core *t, int typed, uint32_t depth, const HistBind *binds) {
  const Machine *m = c->m;
  HistBind node;
  uint32_t i;
  if (t == NULL || !m->has_state)
    return 1;
  switch (t->kind) {
  case CORE_VAR:
  case CORE_NAT:
  case CORE_UNIV:
  case CORE_IZERO:
  case CORE_IONE:
    return 1;
  case CORE_GLOBAL:
    if (typed && history_root(m, t->index))
      return FAIL(c, "REFUSE_HISTORY_WRITE", "a definition with State in its type cannot refer to %s, because the history rule does not check %s (rule D-9)", m->defs[t->index].name, m->defs[t->index].name);
    return 1;
  case CORE_LAM:
  case CORE_PI:
  case CORE_SIGMA:
  case CORE_PLAM:
    return history_ok(c, t->a, typed, depth, binds) && history_ok(c, t->b, typed, depth + 1u, binds);
  case CORE_APP:
  case CORE_INEG:
  case CORE_IMEET:
  case CORE_IJOIN:
    return history_ok(c, t->a, typed, depth, binds) && history_ok(c, t->b, typed, depth, binds);
  case CORE_PATHP:
    return history_ok(c, t->a, typed, depth, NULL) && history_ok(c, t->b, typed, depth + 1u, binds) && history_ok(c, t->args[0], typed, depth, binds) && history_ok(c, t->args[1], typed, depth, binds);
  case CORE_PAPP:
    return history_ok(c, t->a, typed, depth, binds) && history_ok(c, t->b, typed, depth, binds) && history_ok(c, t->args[0], typed, depth, binds) && history_ok(c, t->args[1], typed, depth, binds);
  case CORE_OP:
    break;
  }
  if (t->op == OP_CTOR && m->ctors[t->inst].family == m->state_family) {
    const CtorInfo *ci = &m->ctors[t->inst];
    if (t->argc < ci->field_count)
      return FAIL(c, "REFUSE_HISTORY_WRITE", "%s must have all of its arguments (rule D-9)", ci->name);
    for (i = 0; i < ci->field_count; i++) {
      if (ci->fields[i].history && !history_arg_ok(t->inst, i, t->args[t->argc - ci->field_count + i], depth, binds))
        return FAIL(c, "REFUSE_HISTORY_WRITE", "the history field %s must be (%s t), natAdd (%s t) e, or the variable of bind (natAdd (%s t) e) (rule D-9)", ci->fields[i].name, ci->fields[i].name, ci->fields[i].name, ci->fields[i].name);
    }
  }
  if (t->op == OP_BIND && t->argc == 2u && t->args[0] != NULL && t->args[0]->kind == CORE_OP && t->args[0]->op == OP_NAT_ADD && t->args[0]->argc == 2u && t->args[1] != NULL && t->args[1]->kind == CORE_LAM) {
    node.level = depth;
    node.add = t->args[0];
    node.next = binds;
    return history_ok(c, t->args[0], typed, depth, binds) && history_ok(c, t->args[1]->a, typed, depth, binds) && history_ok(c, t->args[1]->b, typed, depth + 1u, &node);
  }
  for (i = 0; i < t->argc; i++) {
    if (!history_ok(c, t->args[i], typed, depth, binds))
      return 0;
  }
  return 1;
}

/* The design signature (PLAN section 4; USER ruling Q-S1-3 (a)). A slot is
   a base sort: a program definition of a slot must have the type Type 0. A
   defined name is a name that the kernel gives at its slice (PLAN section
   12). The word `in` is not a row: programs use it as a name. */
typedef enum {
  SIG_SLOT,
  SIG_DEFINED,
  /* A program name with a kernel-fixed type (USER ruling Q-S4-6 (a)): the
     program defines it, and check_sig checks its type. */
  SIG_PROGRAM
} SigKind;

typedef struct {
  const char *name;
  SigKind kind;
} SigRow;

static const SigRow SIGNATURE[] = {
  /* The base sorts (PLAN section 4): slots of the type Type 0. */
  {"Asset", SIG_SLOT},
  {"Owner", SIG_SLOT},
  {"Key", SIG_SLOT},
  {"Val", SIG_SLOT},
  {"Node", SIG_SLOT},
  {"OutRef", SIG_SLOT},
  {"Output", SIG_SLOT},
  {"Query", SIG_SLOT},
  {"Answer", SIG_SLOT},
  /* The kernel gives these names at slice S2 (PLAN section 12). */
  {"Amount", SIG_DEFINED},
  {"Maybe", SIG_DEFINED},
  {"Bag", SIG_DEFINED},
  {"Value", SIG_DEFINED},
  {"Balance", SIG_DEFINED},
  {"Delta", SIG_DEFINED},
  {"Balanced", SIG_DEFINED},
  {"neg", SIG_DEFINED},
  /* The kernel gives these names at slice S3 (PLAN section 12). */
  {"Pfin", SIG_DEFINED},
  {"Mempool", SIG_DEFINED},
  {"union", SIG_DEFINED},
  {"Footprint", SIG_DEFINED},
  /* Slice S4 (PLAN section 12). Body, Witness, Digest and Sig are slots,
     and witnessOk, txid, the six bagFold arguments sigIsSet .. sigUnitL
     and the node names nodeEq, quorum and signs are program names with a
     kernel-fixed type (USER rulings Q-S4-1 (a), Q-S4-3 (a), Q-S4-4 (a),
     Q-S4-5 (a), Q-S4-6 (a) and Q-S4-8 (a)). The kernel gives the other
     names. */
  {"Body", SIG_SLOT},
  {"Witness", SIG_SLOT},
  {"Digest", SIG_SLOT},
  {"witnessOk", SIG_PROGRAM},
  {"txid", SIG_PROGRAM},
  {"Authorized", SIG_DEFINED},
  {"AuthTx", SIG_DEFINED},
  {"Sig", SIG_SLOT},
  {"sigIsSet", SIG_PROGRAM},
  {"sigOne", SIG_PROGRAM},
  {"sigMul", SIG_PROGRAM},
  {"sigAssoc", SIG_PROGRAM},
  {"sigComm", SIG_PROGRAM},
  {"sigUnitL", SIG_PROGRAM},
  {"nodeEq", SIG_PROGRAM},
  {"quorum", SIG_PROGRAM},
  {"signs", SIG_PROGRAM},
  {"QC", SIG_DEFINED},
  {"agg", SIG_DEFINED},
  /* The kernel gives these names at slice S5 (PLAN section 12). */
  {"Ind", SIG_DEFINED},
  {"reads", SIG_DEFINED},
  {"writes", SIG_DEFINED},
  /* The kernel gives these names at slice S6 (PLAN section 12). */
  {"Trace", SIG_DEFINED},
  {"Eff", SIG_DEFINED},
  {"Blockchain", SIG_DEFINED},
  /* The kernel gives these names at slice S7 (PLAN section 12). */
  {"Ledger", SIG_DEFINED},
  {"Compatible", SIG_DEFINED},
  {"apply", SIG_DEFINED},
  {"query", SIG_DEFINED},
  /* The kernel gives these names at slice S8 (PLAN section 12). */
  {"FinMap", SIG_DEFINED},
  {"UTxO", SIG_DEFINED},
  {"Valid", SIG_DEFINED},
  {"canon", SIG_DEFINED},
  {"root", SIG_DEFINED},
  {"compose", SIG_DEFINED},
};

#define SIG_COUNT ((uint32_t)(sizeof SIGNATURE / sizeof SIGNATURE[0]))

static uint32_t sig_row(const char *name) {
  uint32_t i;
  for (i = 0; i < SIG_COUNT && strcmp(SIGNATURE[i].name, name) != 0; i++)
    ;
  return i;
}

/* The slots that must be first-order data: Asset (valueCount counts with
   the conversion check, USER ruling Q-S2-5 (a)), Key (Footprint is Pfin
   Key, USER ruling Q-S3-2 (a)), Body and Witness (USER ruling Q-S4-1
   (a)), and Digest (USER ruling Q-S4-3 (a)). */
static int first_order_slot(const char *name) {
  return strcmp(name, "Asset") == 0 || strcmp(name, "Key") == 0 || strcmp(name, "Body") == 0 || strcmp(name, "Witness") == 0 || strcmp(name, "Digest") == 0;
}

/* The names that a Body must not mention: txid reads the body only (law
   L5, PLAN section 6, USER ruling Q-S4-2 (a)). */
static int witness_name(const char *name) {
  return strcmp(name, "Witness") == 0 || strcmp(name, "Authorized") == 0 || strcmp(name, "AuthTx") == 0;
}

/* Law L5 (S4, USER ruling Q-S4-2 (a)). 1 if the core term T mentions
   Witness, Authorized or AuthTx, also through the body of a program def. */
static int mentions_witness(const Machine *m, const Core *t) {
  uint32_t i;
  if (t == NULL)
    return 0;
  switch (t->kind) {
  case CORE_VAR:
  case CORE_NAT:
  case CORE_UNIV:
  case CORE_IZERO:
  case CORE_IONE:
    return 0;
  case CORE_GLOBAL:
    return witness_name(m->defs[t->index].name) || (m->defs[t->index].origin == ORIGIN_PROGRAM && mentions_witness(m, m->defs[t->index].body));
  case CORE_LAM:
  case CORE_PI:
  case CORE_SIGMA:
  case CORE_APP:
  case CORE_PLAM:
  case CORE_INEG:
  case CORE_IMEET:
  case CORE_IJOIN:
    return mentions_witness(m, t->a) || mentions_witness(m, t->b);
  case CORE_PATHP:
  case CORE_PAPP:
    return mentions_witness(m, t->a) || mentions_witness(m, t->b) || mentions_witness(m, t->args[0]) || mentions_witness(m, t->args[1]);
  case CORE_OP:
    break;
  }
  for (i = 0; i < t->argc; i++) {
    if (mentions_witness(m, t->args[i]))
      return 1;
  }
  return 0;
}

/* The index of the def NAME in M, or the def count. */
static uint32_t sig_def_index(const Machine *m, const char *name) {
  uint32_t k;
  for (k = 0; k < m->def_count && strcmp(m->defs[k].name, name) != 0; k++)
    ;
  return k;
}

/* The value of the def K, as the evaluator gives a CORE_GLOBAL. */
static const Value *sig_global_value(Machine *m, uint32_t k) {
  Core g;
  memset(&g, 0, sizeof g);
  g.kind = CORE_GLOBAL;
  g.index = k;
  return eval_core(m, NULL, &g);
}

/* The type value of the sig name NAME: the value of the def NAME, else the
   type value of the family NAME (a TERM_VAR, check_type, then here, as
   step_type gives it). USER ruling Q-S5-31 (a): the generated Body is a
   family, not a def. NULL if NAME has no def and no family. */
static const Value *sig_name_value(Checker *c, const char *name) {
  Machine *m = c->m;
  uint32_t k = sig_def_index(m, name);
  Term v;
  uint64_t level = 0;
  const Core *t;
  if (k != m->def_count)
    return sig_global_value(m, k);
  if (find_family(m, name) == NO_FAMILY)
    return NULL;
  memset(&v, 0, sizeof v);
  v.kind = TERM_VAR;
  v.name = name;
  t = check_type(c, &v, &level);
  return t == NULL ? NULL : here(c, t);
}

/* The codomain of the function type TV at the level LEVEL, if the domain
   of TV converts with the type value of the sig name NAME; NULL if not. */
static const Value *sig_arrow(Checker *c, const Value *tv, uint32_t level, const char *name) {
  Machine *m = c->m;
  const Value *want = tv == NULL || tv->kind != VAL_PI ? NULL : sig_name_value(c, name);
  if (want == NULL || !conv_values(m, level, tv->dom, want))
    return NULL;
  return closure_apply(m, tv, val_var(m, level));
}

/* REFUSE_EQ_UNDECIDABLE (quotient-lang S6 u8, N7, USER rulings Q-S6-6
   (a), Q-S6-39 (b) and Q-S6-40 (a)): a program def of the type
   A -> A -> C, with A one of EQ_UNDECIDABLE and C one of EQ_CODOMAINS, is
   an equality test on A, and equality on A is not decidable. The test
   reads the type value, so an alias of A and the form
   (a : A) -> (b : A) -> C give the same code. Only the curried form has
   the test (Q-S6-40 (a)). A name that is not in scope (Blockchain with no
   Trace) has no test. Flag, Sum and Unit are core names, not defs or
   families, so sig_name_value gives NULL for them: the codomain values
   come from check_type of a made term. */
static const char *const EQ_UNDECIDABLE[] = {"Eff", "Blockchain"};
static const char *const EQ_CODOMAINS[] = {"Flag", "Sum Unit Unit"};

/* The type value of the closed type term T, as check_type gives it; NULL
   if T does not check. The diagnostic of a failed check is not kept. */
static const Value *eq_type_value(Checker *c, const Term *t) {
  Diag saved = *c->m->diag;
  uint64_t level = 0;
  const Core *k = check_type(c, t, &level);
  if (k == NULL)
    *c->m->diag = saved;
  return k == NULL ? NULL : here(c, k);
}

static int eq_decidable(Checker *c, const Decl *d, const Value *tv) {
  Term flag;
  Term sum;
  Term unit;
  Term half;
  Term either;
  const Value *cods[2];
  size_t i;
  size_t j;
  memset(&flag, 0, sizeof flag);
  memset(&sum, 0, sizeof sum);
  memset(&unit, 0, sizeof unit);
  memset(&half, 0, sizeof half);
  memset(&either, 0, sizeof either);
  flag.kind = TERM_VAR;
  flag.name = "Flag";
  sum.kind = TERM_VAR;
  sum.name = "Sum";
  unit.kind = TERM_VAR;
  unit.name = "Unit";
  half.kind = TERM_APP;
  half.left = &sum;
  half.right = &unit;
  either.kind = TERM_APP;
  either.left = &half;
  either.right = &unit;
  cods[0] = eq_type_value(c, &flag);
  cods[1] = eq_type_value(c, &either);
  for (i = 0u; i < sizeof EQ_UNDECIDABLE / sizeof EQ_UNDECIDABLE[0]; i++) {
    const char *a = EQ_UNDECIDABLE[i];
    const Value *rest = sig_arrow(c, tv, c->level, a);
    const Value *cod = rest == NULL ? NULL : sig_arrow(c, rest, c->level + 1u, a);
    for (j = 0u; cod != NULL && j < sizeof cods / sizeof cods[0]; j++)
      if (cods[j] != NULL && conv_values(c->m, c->level + 2u, cod, cods[j]))
        return FAIL(c, "REFUSE_EQ_UNDECIDABLE", "%s has the type %s -> %s -> %s: equality on %s is not decidable, so a program cannot test it (N7, USER rulings Q-S6-6 (a), Q-S6-39 (b))", d->name, a, a, EQ_CODOMAINS[j], a);
  }
  return 1;
}

/* The bagFold arguments after A and M, in the bagFold order (USER
   rulings Q-S4-4 (a) and Q-S4-6 (a)). A program with the slot Sig gives
   each of them, and the front end gives agg after the last of them. */
static const char *const SIG_ARGS[] = {"sigIsSet", "sigOne", "sigMul", "sigAssoc", "sigComm", "sigUnitL"};

#define SIG_ARG_COUNT (sizeof SIG_ARGS / sizeof SIG_ARGS[0])

/* 1 if NAME is a bagFold argument at Sig. */
static int sig_arg_name(const char *name) {
  size_t i;
  for (i = 0; i < SIG_ARG_COUNT && strcmp(SIG_ARGS[i], name) != 0; i++)
    ;
  return i < SIG_ARG_COUNT;
}

/* The codomain of the function type TV at ARG; NULL if TV is not a
   function type. */
static const Value *sig_apply(Machine *m, const Value *tv, const Value *arg) {
  return (tv == NULL || tv->kind != VAL_PI) ? NULL : closure_apply(m, tv, arg);
}

/* 1 if TV converts with the type of the bagFold argument NAME at Sig: the
   domain of the bagFold type at A := Sig, M := Sig and the earlier
   arguments. An earlier argument is its def. If the program does not
   define it before NAME, it is the fresh variable at the level of C,
   which TV cannot name, so a type that needs it does not convert. */
static int sig_arg_ok(Checker *c, const char *name, const Value *tv) {
  Machine *m = c->m;
  uint32_t fold = sig_def_index(m, "bagFold");
  uint32_t sig = sig_def_index(m, "Sig");
  const Value *want;
  size_t i;
  if (fold == m->def_count || sig == m->def_count)
    return 0;
  want = sig_apply(m, sig_apply(m, m->defs[fold].type, sig_global_value(m, sig)), sig_global_value(m, sig));
  for (i = 0; i < SIG_ARG_COUNT && want != NULL && strcmp(SIG_ARGS[i], name) != 0; i++) {
    uint32_t k = sig_def_index(m, SIG_ARGS[i]);
    want = sig_apply(m, want, k == m->def_count ? val_var(m, c->level) : sig_global_value(m, k));
  }
  return i < SIG_ARG_COUNT && want != NULL && want->kind == VAL_PI && conv_values(m, c->level + 1u, tv, want->dom);
}

/* 1 if a program declaration of the checked list has the name NAME. */
static int program_defines(const Checker *c, const char *name) {
  size_t i;
  for (i = 0; i < c->decls->count && !(c->decls->items[i].origin == ORIGIN_PROGRAM && strcmp(c->decls->items[i].name, name) == 0); i++)
    ;
  return i < c->decls->count;
}

/* Q-S5-6 (a) and Q-S5-8 (a): 1 if the program declares a footprint
   family. Then the slot Body is the sum of the footprint families, and a
   program def of Body is REFUSE_SIG. The scan covers all the program
   declarations, so the order of the def and the family does not matter. */
static int program_footprint(const Checker *c) {
  size_t i;
  for (i = 0; i < c->decls->count && !(c->decls->items[i].origin == ORIGIN_PROGRAM && c->decls->items[i].kind == DECL_FAMILY && c->decls->items[i].footprint != NULL); i++)
    ;
  return i < c->decls->count;
}

/* Q-S5-23 (a): 1 if the program declares a key space. Then Key is the
   generated family of the key spaces, and a program def of Key is
   REFUSE_SIG (kernel_sig). The scan covers all the program declarations,
   so the order of the def and the key space does not matter. */
static int program_keyspace(const Checker *c) {
  size_t i;
  for (i = 0; i < c->decls->count && !(c->decls->items[i].origin == ORIGIN_PROGRAM && c->decls->items[i].kind == DECL_KEYSPACE); i++)
    ;
  return i < c->decls->count;
}

/* The domains of the node names nodeEq and signs (USER ruling Q-S4-5
   (a)). Each one is a def of the program. */
static const char *const NODE_EQ_DOMS[] = {"Node", "Node"};
static const char *const SIGNS_DOMS[] = {"Node", "Body", "Sig"};

/* 1 if TV is the function type from the defs NAMES, in this order, to the
   type of btrue. Each domain converts with the def of its name, at one
   level more than the domain before it. */
static int sig_bit_arrows(Checker *c, const Value *tv, const char *const *names, uint32_t count) {
  Machine *m = c->m;
  uint32_t bit = sig_def_index(m, "btrue");
  const Value *cod = tv;
  uint32_t i;
  for (i = 0; i < count && cod != NULL; i++)
    cod = sig_arrow(c, cod, c->level + i, names[i]);
  return bit != m->def_count && cod != NULL && conv_values(m, c->level + count, cod, m->defs[bit].type);
}

/* 1 if TV converts with Pfin Node -> Sum Unit Unit (USER ruling Q-S4-5
   (a)): the type of pfinIn at A := Node after the equality and the
   element. That type does not contain them, so each one is the fresh
   variable at the level of C. */
static int quorum_ok(Checker *c, const Value *tv) {
  Machine *m = c->m;
  uint32_t in = sig_def_index(m, "pfinIn");
  uint32_t node = sig_def_index(m, "Node");
  const Value *want;
  if (in == m->def_count || node == m->def_count)
    return 0;
  want = sig_apply(m, sig_apply(m, sig_apply(m, m->defs[in].type, sig_global_value(m, node)), val_var(m, c->level)), val_var(m, c->level));
  return want != NULL && conv_values(m, c->level + 1u, tv, want);
}

/* The kernel-fixed type of a program name of the kind SIG_PROGRAM. USER
   ruling Q-S4-6 (a): witnessOk must have the type Body -> Witness -> Sum
   Unit Unit (the codomain converts with the type of btrue). USER rulings
   Q-S4-2 (a) and Q-S4-8 (a): txid must have the type Body -> Digest (the
   codomain converts with the def Digest). The domains convert with the
   defs Body and Witness. USER rulings Q-S4-4 (a) and Q-S4-6 (a): the six
   bagFold arguments must have their bagFold types at Sig. USER ruling
   Q-S4-5 (a): nodeEq, quorum and signs must have the types Node -> Node
   -> Sum Unit Unit, Pfin Node -> Sum Unit Unit and Node -> Body -> Sig ->
   Sum Unit Unit. */
static int program_type(Checker *c, const char *name, const Value *tv) {
  Machine *m = c->m;
  uint32_t bit = sig_def_index(m, "btrue");
  uint32_t digest = sig_def_index(m, "Digest");
  const Value *cod = sig_arrow(c, tv, c->level, "Body");
  if (sig_arg_name(name))
    return sig_arg_ok(c, name, tv);
  if (strcmp(name, "nodeEq") == 0)
    return sig_bit_arrows(c, tv, NODE_EQ_DOMS, 2u);
  if (strcmp(name, "quorum") == 0)
    return quorum_ok(c, tv);
  if (strcmp(name, "signs") == 0)
    return sig_bit_arrows(c, tv, SIGNS_DOMS, 3u);
  if (strcmp(name, "txid") == 0)
    return digest != m->def_count && cod != NULL && conv_values(m, c->level + 1u, cod, sig_global_value(m, digest));
  cod = sig_arrow(c, cod, c->level + 1u, "Witness");
  return bit != m->def_count && cod != NULL && conv_values(m, c->level + 2u, cod, m->defs[bit].type);
}

/* A program definition of a slot must have the type Type 0, and a
   first-order slot must be first-order data. The slot Body must not
   mention a witness name (law L5). A program name with a kernel-fixed
   type must have that type: another type of txid is REFUSE_WITNESS_READ
   (law L5). Another type of sigComm, or a slot Sig with no sigComm, is
   REFUSE_BAG_NONCOMM (law L1). A program declaration of a defined name
   does not get here:
   kernel_sig refuses it before the name check. */
static int check_sig(Checker *c, const Decl *d, const Value *tv, const Core *body) {
  uint32_t i = sig_row(d->name);
  if (d->origin == ORIGIN_PROGRAM && !eq_decidable(c, d, tv))
    return 0;
  if (d->origin != ORIGIN_PROGRAM || i == SIG_COUNT)
    return 1;
  switch (SIGNATURE[i].kind) {
  case SIG_SLOT:
    if (!conv_values(c->m, c->level, tv, val_univ(c->m, 0u)))
      return FAIL(c, "REFUSE_SIG", "the slot %s must have the type Type 0 (PLAN section 4)", d->name);
    if (strcmp(d->name, "Sig") == 0 && !program_defines(c, "sigComm"))
      return FAIL(c, "REFUSE_BAG_NONCOMM", "agg at Bag Sig needs sigComm, the commutative clause (law L1, O2): the program does not define sigComm (PLAN section 4, USER ruling Q-S4-4 (a))");
    if (strcmp(d->name, "Body") == 0 && mentions_witness(c->m, body))
      return FAIL(c, "REFUSE_WITNESS_READ", "the slot Body must not mention Witness, Authorized or AuthTx: txid reads the body only (law L5, PLAN section 6, USER ruling Q-S4-2 (a))");
    return (!first_order_slot(d->name) || asset_first_order(c->m, here(c, body), 0u)) ? 1 : FAIL(c, "REFUSE_SIG", "the slot %s must be first-order data: no path constructor and no function (PLAN section 4, USER rulings Q-S2-5 (a) and Q-S3-2 (a))", d->name);
  case SIG_PROGRAM:
    if (strcmp(d->name, "txid") == 0)
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_WITNESS_READ", "txid must have the type Body -> Digest: txid reads the body only (law L5, PLAN section 6, USER rulings Q-S4-2 (a) and Q-S4-8 (a))");
    if (strcmp(d->name, "sigComm") == 0)
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_BAG_NONCOMM", "agg at Bag Sig needs sigComm, the commutative clause (law L1, O2): sigComm must have the type (x : Sig) -> (y : Sig) -> Path Sig (sigMul x y) (sigMul y x) (PLAN section 4, USER rulings Q-S4-4 (a) and Q-S4-6 (a))");
    if (strcmp(d->name, "nodeEq") == 0)
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_SIG", "nodeEq must have the type Node -> Node -> Sum Unit Unit (PLAN section 4, USER rulings Q-S4-5 (a) and Q-S4-6 (a))");
    if (strcmp(d->name, "quorum") == 0)
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_SIG", "quorum must have the type Pfin Node -> Sum Unit Unit (PLAN section 4, USER rulings Q-S4-5 (a) and Q-S4-6 (a))");
    if (strcmp(d->name, "signs") == 0)
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_SIG", "signs must have the type Node -> Body -> Sig -> Sum Unit Unit (PLAN section 4, USER rulings Q-S4-5 (a) and Q-S4-6 (a))");
    if (sig_arg_name(d->name))
      return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_SIG", "%s must have the type of its bagFold argument at Sig, after the earlier bagFold arguments (PLAN section 4, USER rulings Q-S4-4 (a) and Q-S4-6 (a))", d->name);
    return program_type(c, d->name, tv) ? 1 : FAIL(c, "REFUSE_SIG", "witnessOk must have the type Body -> Witness -> Sum Unit Unit (PLAN section 4, USER ruling Q-S4-6 (a))");
  case SIG_DEFINED:
    break;
  }
  return 1;
}

/* A program declaration of a defined name of the design signature is
   REFUSE_SIG, before the name check, so the code is the same before and
   after the kernel gives the name. */
static int kernel_sig(Checker *c, const Decl *d) {
  uint32_t i = sig_row(d->name);
  if (d->origin != ORIGIN_PROGRAM || i == SIG_COUNT)
    return 1;
  switch (SIGNATURE[i].kind) {
  case SIG_DEFINED:
    return FAIL(c, "REFUSE_SIG", "%s is a defined name of the design signature (PLAN section 4); the kernel gives it at its slice (PLAN section 12)", d->name);
  case SIG_SLOT:
    /* Q-S5-8 (a) (u4v): as for Key, a program def of Body gives REFUSE_SIG
       before and after the generated Body family (front.c body_family). */
    if (d->kind == DECL_DEF && d->origin == ORIGIN_PROGRAM && strcmp(d->name, "Body") == 0 && program_footprint(c))
      return FAIL(c, "REFUSE_SIG", "the slot Body is the sum of the footprint families (Q-S5-6 (a)): a program with a footprint family must not define Body (Q-S5-8 (a))");
    /* Q-S5-23 (a): with a key space in the program, the front end makes
       Key (key_family). This rule is before name_free, so a program def
       of Key gives REFUSE_SIG before and after the generated family. */
    if (strcmp(d->name, "Key") == 0 && d->kind == DECL_DEF && program_keyspace(c))
      return FAIL(c, "REFUSE_SIG", "the slot Key is the generated family of the key spaces (Q-S5-23 (a)): a program with a key space must not define Key");
    break;
  case SIG_PROGRAM:
    break;
  }
  return 1;
}

static uint32_t find_family(const Machine *m, const char *name);

/* Rule O7 (S5, Q-S5-2 (a)). 1 if the core term T uses a law-only name: a
   law-only def, or an elim, a fold or a projection of a sealed family. The
   arguments of the type former TRUNC (Trunc1) are skipped: an end point
   under Trunc1 comes out only into a proposition. */
static int law_uses(const Machine *m, uint32_t trunc, const Core *t) {
  uint32_t i;
  if (t == NULL)
    return 0;
  switch (t->kind) {
  case CORE_VAR:
  case CORE_NAT:
  case CORE_UNIV:
  case CORE_IZERO:
  case CORE_IONE:
    return 0;
  case CORE_GLOBAL:
    return m->defs[t->index].law_only;
  case CORE_LAM:
  case CORE_PI:
  case CORE_SIGMA:
  case CORE_APP:
  case CORE_PLAM:
  case CORE_INEG:
  case CORE_IMEET:
  case CORE_IJOIN:
    return law_uses(m, trunc, t->a) || law_uses(m, trunc, t->b);
  case CORE_PATHP:
  case CORE_PAPP:
    return law_uses(m, trunc, t->a) || law_uses(m, trunc, t->b) || law_uses(m, trunc, t->args[0]) || law_uses(m, trunc, t->args[1]);
  case CORE_OP:
    break;
  }
  if (t->op == OP_FAMILY && t->inst == trunc)
    return 0;
  /* OP_ELIM keeps the family + 1 in FIELD (0 for Sum and Unit). */
  if ((t->op == OP_FOLD_FAMILY && m->families[t->inst].sealed) || (t->op == OP_ELIM && t->field != 0u && m->families[t->field - 1u].sealed) || (t->op == OP_PROJ && m->families[m->ctors[t->inst].family].sealed))
    return 1;
  for (i = 0; i < t->argc; i++) {
    if (law_uses(m, trunc, t->args[i]))
      return 1;
  }
  return 0;
}

/* Rule O7: a law type is, after the Pis (the loop of entry_of), a Path type
   or Trunc1 X. */
static int law_type(Machine *m, uint32_t level, uint32_t trunc, const Value *t) {
  uint32_t n = level;
  while (t != NULL && t->kind == VAL_PI)
    t = closure_apply(m, t, val_var(m, n++));
  return t != NULL && (t->kind == VAL_PATHP || is_family(t, trunc));
}

/* Register a checked body, including the closed label cores retained by
   cocell_shape. Both callers obtain BODY from the term checker. */
static int check_def_body(Checker *c, const Decl *d, const Value *tv, const Core *syntax_type, const Core *body) {
  Machine *m = c->m;
  DefInfo *info = &m->defs[m->def_count];
  uint32_t trunc = find_family(m, "Trunc1");
  int program = d->origin == ORIGIN_PROGRAM;
  const Core *tc;
  int law;
  if (body == NULL || !check_sig(c, d, tv, body))
    return 0;
  if (has_history(m) && strcmp(d->name, "init") != 0 && !is_family(tv, m->state_family) && !history_ok(c, body, mentions_state(m, c->level, tv), 0, NULL))
    return 0;
  /* Rule O7 (S5): the domain marks its law defs; a program def is law-only
     when its type or its body uses a law-only name. Kit mode sets the flag
     but does not refuse. */
  tc = program ? quote_value(m, c->level, tv) : NULL;
  if (program && tc == NULL)
    return FAIL(c, "OOM", "out of memory");
  law = program ? law_uses(m, trunc, syntax_type) || law_uses(m, trunc, tc) || law_uses(m, trunc, body) : d->is_law;
  if (law && guest(c) && !law_type(m, c->level, trunc, tv))
    return FAIL(c, "REFUSE_LAW", "%s uses a law-only name (decrypt, observe, an elim, fold or projection of a sealed family) but its type is not a law (a Path or Trunc1 codomain); rule O7", d->name);
  info->name = d->name;
  info->origin = d->origin;
  info->body = body;
  info->type = tv;
  info->value = NULL;
  info->law_only = law;
  m->def_count++;
  return 1;
}

static int check_def(Checker *c, const Decl *d) {
  uint64_t level = 0;
  const Core *t = check_type(c, d->type, &level);
  const Value *tv = here(c, t);
  const Core *body = check(c, d->body, tv);
  return check_def_body(c, d, tv, t, body);
}

/* First order (slice K3a): Nat, Flag, and Option, Prod and List
   of first-order types, after normalization. */
static int first_order(const Value *t) {
  uint32_t i;
  if (t == NULL || t->kind != VAL_OP)
    return 0;
  if (t->op == OP_NAT || t->op == OP_FLAG)
    return 1;
  if (t->op != OP_OPTION && t->op != OP_PROD && t->op != OP_LIST)
    return 0;
  for (i = 0; i < t->argc; i++) {
    if (!first_order(t->args[i]))
      return 0;
  }
  return 1;
}

/* The state form (slice K3a): one `state State` with no parameters, one
   constructor and first-order fields. A history field is a Nat. */
static int check_state(Checker *c, const Decl *d) {
  Machine *m = c->m;
  CtorInfo *ci;
  FieldInfo *fields;
  const Env *env = c->env;
  uint32_t j;
  if (m->has_state)
    return FAIL(c, "REFUSE_STATE", "a program can declare one state only");
  if (strcmp(d->name, "State") != 0)
    return FAIL(c, "REFUSE_STATE", "the state type must have the name State, found %s", d->name);
  if (d->param_count != 0u || d->ctor_count != 1u || d->index != NULL)
    return FAIL(c, "REFUSE_STATE", "the state must have no parameters or index telescope and one constructor");
  if (!name_free(c, d->name) || !check_family(c, d))
    return 0;
  ci = &m->ctors[m->families[m->family_count - 1u].first_ctor];
  fields = arena_alloc(m->arena, ((size_t)ci->field_count + 1u) * sizeof *fields);
  if (fields == NULL)
    return FAIL(c, "OOM", "out of memory");
  for (j = 0; j < ci->field_count; j++) {
    const Value *t = eval_core(m, env, ci->fields[j].type);
    if (t == NULL)
      return 0;
    if (!first_order(t) && !val_is(t, OP_KMAP))
      return FAIL(c, "REFUSE_STATE", "the state field %s must have a first-order type: Nat, Flag, Option, Prod or List of them, or a Map K V", ci->fields[j].name);
    if (ci->fields[j].history && t->op != OP_NAT)
      return FAIL(c, "REFUSE_STATE", "the history field %s must have the type Nat", ci->fields[j].name);
    /* First-order state types are closed after normalization. Keep that
       form for lowering, which reads them without a field environment. */
    fields[j] = ci->fields[j];
    fields[j].type = quote_value(m, c->level, t);
    fields[j].dependent = 0;
    env = env_push(m, env, val_var(m, c->level + j));
    if (fields[j].type == NULL || env == NULL)
      return 0;
  }
  ci->fields = fields;
  m->has_state = 1;
  m->state_family = m->family_count - 1u;
  return 1;
}

/* The fields of a cocell signature (S4, rule R1): the one observation `A`,
   a cofield `D A`, or a labelled cofield `E -> D A` with E closed. */
typedef enum {
  COCELL_OBSERVATION,
  COCELL_COFIELD,
  COCELL_LABELLED
} CocellField;

/* T is the application of the variable of index F to the variable of
   index A. */
static int cocell_app(const Core *t, uint32_t f, uint32_t a) {
  return t->kind == CORE_APP && t->a->kind == CORE_VAR && t->a->index == f && t->b->kind == CORE_VAR && t->b->index == a;
}

/* The kind of FIELD J with the normal type T, in the context D, A, then the
   J earlier fields: A is the variable J and D is the variable J + 1. A
   labelled cofield is an arrow written in the field. */
static int cocell_kind(const Field *field, const Core *t, uint32_t j, CocellField *out) {
  if (t->kind == CORE_VAR && t->index == j) {
    *out = COCELL_OBSERVATION;
    return 1;
  }
  if (cocell_app(t, j + 1u, j)) {
    *out = COCELL_COFIELD;
    return 1;
  }
  if (field->type->kind == TERM_PI && t->kind == CORE_PI && cell_closed(t->a, 0u) && cocell_app(t->b, j + 2u, j + 1u)) {
    *out = COCELL_LABELLED;
    return 1;
  }
  return 0;
}

/* The shape check of `cofamily D (A : Type n) := c fields` (S4, rule R1):
   one declaration, one type parameter, no index, one clause, and each
   field a kind of CocellField, with exactly one observation. The fields
   are checked with D : Type n -> Type n and A as locals. The universe of
   the parameter goes to *N, the field kinds to KINDS and the universe of
   each label type to LABELS, with its closed normal form in LABEL_TYPES. */
static int cocell_shape(Checker *c, const Decl *d, uint64_t *n, CocellField *kinds, uint64_t *labels, const Core **label_types) {
  Machine *m = c->m;
  const Ctor *ctor = d->ctors;
  Term *arrow = arena_alloc(m->arena, sizeof *arrow);
  const Core *pt, *pn, *dt;
  uint64_t level = 0;
  uint32_t j, observations = 0;
  if (arrow == NULL)
    return FAIL(c, "OOM", "out of memory");
  if (d->block_count > 1u)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: it is in an and block; a type constructor is one signature (rule R1)", d->name);
  if (d->param_count != 1u)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: it has %u parameters; a cocell signature has one type parameter (rule R1)", d->name, (unsigned)d->param_count);
  if (d->index != NULL)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: it has a type index (rule R1)", d->name);
  if (d->ctor_count != 1u || ctor->result != NULL || ctor->boundary != NULL)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: it must have one clause, with no result and no boundary (rule R1)", d->name);
  pt = check_type(c, d->params[0].type, &level);
  if (pt == NULL)
    return 0;
  pn = quote_value(m, c->level, here(c, pt));
  if (pn == NULL)
    return FAIL(c, "OOM", "out of memory");
  if (pn->kind != CORE_UNIV)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: the parameter %s is not a universe; a cocell signature has one type parameter (rule R1)", d->name, d->params[0].name);
  *n = pn->nat;
  memset(arrow, 0, sizeof *arrow);
  arrow->kind = TERM_PI;
  arrow->line = d->line;
  arrow->col = d->col;
  arrow->left = d->params[0].type;
  arrow->right = d->params[0].type;
  dt = check_type(c, arrow, &level);
  if (dt == NULL || !push(c, d->name, here(c, dt)) || !push(c, d->params[0].name, here(c, pt)))
    return 0;
  for (j = 0; j < ctor->field_count; j++) {
    const Field *field = &ctor->fields[j];
    const Core *k = check_type(c, field->type, &level);
    const Core *t = k == NULL ? NULL : quote_value(m, c->level, here(c, k));
    if (k == NULL)
      return 0;
    if (t == NULL)
      return FAIL(c, "OOM", "out of memory");
    if (!cocell_kind(field, t, j, &kinds[j]))
      return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: the field %s must be the observation %s, the cofield %s %s or a labelled cofield E -> %s %s with E closed (rule R1)",
                  d->name, field->name, d->params[0].name, d->name, d->params[0].name, d->name, d->params[0].name);
    labels[j] = 0;
    if (kinds[j] == COCELL_LABELLED && check_type(c, field->type->left, &labels[j]) == NULL)
      return 0;
    if (labels[j] > *n)
      return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: the label type of %s is in Type %llu, above Type %llu of %s (rule R1)",
                  d->name, field->name, (unsigned long long)labels[j], (unsigned long long)*n, d->params[0].name);
    /* cocell_kind proved this domain closed. Keep its checked normal form
       rather than resolving the original syntax in a different scope. */
    label_types[j] = kinds[j] == COCELL_LABELLED ? t->a : NULL;
    observations += kinds[j] == COCELL_OBSERVATION;
    if (!push(c, field->name, here(c, k)))
      return 0;
  }
  if (observations != 1u)
    return FAIL(c, "REFUSE_CELL", "%s is not a cocell signature: it has %u observations; a cocell signature has exactly one (rule R1)", d->name, (unsigned)observations);
  for (j = 0; j < ctor->field_count; j++)
    if (!name_free(c, ctor->fields[j].name))
      return 0;
  return name_free(c, ctor->name);
}

/* The text of the declarations of a cofamily (S4): a two-pass appender.
   With TEXT NULL it only measures; then it writes into CAP bytes. */
typedef struct {
  char *text;
  size_t len;
  size_t cap;
} Text;

static void text_add(Text *t, const char *format, ...) {
  va_list ap;
  int n;
  va_start(ap, format);
  n = vsnprintf(t->text == NULL ? NULL : t->text + t->len, t->text == NULL ? 0u : t->cap - t->len, format, ap);
  va_end(ap);
  t->len += n > 0 ? (size_t)n : 0u;
}

/* The position constructor of field F of the cofamily DN. */
static void cocell_pos(Text *t, const char *dn, const char *f, CocellField kind) {
  switch (kind) {
  case COCELL_OBSERVATION:
    break;
  case COCELL_COFIELD:
    text_add(t, " | %s.%s (%s.%s.rest : %s.pos)", dn, f, dn, f, dn);
    break;
  case COCELL_LABELLED:
    text_add(t, " | %s.%s (%s.%s.label : %s.%s.E) (%s.%s.rest : %s.pos)", dn, f, dn, f, dn, f, dn, f, dn);
    break;
  }
}

/* The destructor F: the observation reads the position here, a cofield
   moves one position down. */
static void cocell_dtor(Text *t, const char *dn, const char *f, CocellField kind, unsigned long long u) {
  switch (kind) {
  case COCELL_OBSERVATION:
    text_add(t, "def %s : (.A : Type %llu) -> %s .A -> .A := fun (.A : Type %llu) (.x : %s .A) => .x %s.here\n", f, u, dn, u, dn, dn);
    break;
  case COCELL_COFIELD:
    text_add(t, "def %s : (.A : Type %llu) -> %s .A -> %s .A := fun (.A : Type %llu) (.x : %s .A) (.p : %s.pos) => .x (%s.%s .p)\n",
             f, u, dn, dn, u, dn, dn, dn, f);
    break;
  case COCELL_LABELLED:
    text_add(t, "def %s : (.A : Type %llu) -> %s .A -> %s.%s.E -> %s .A := fun (.A : Type %llu) (.x : %s .A) (.e : %s.%s.E) (.p : %s.pos) => .x (%s.%s .e .p)\n",
             f, u, dn, dn, f, dn, u, dn, dn, f, dn, dn, f);
    break;
  }
}

/* The step binder of cofield F for the walk and the corecursor, then
   SUFFIX. */
static void cocell_step(Text *t, const char *dn, const char *f, CocellField kind, const char *suffix) {
  switch (kind) {
  case COCELL_OBSERVATION:
    break;
  case COCELL_COFIELD:
    text_add(t, " (.t.%s : .S -> .S)%s", f, suffix);
    break;
  case COCELL_LABELLED:
    text_add(t, " (.t.%s : .S -> %s.%s.E -> .S)%s", f, dn, f, suffix);
    break;
  }
}

/* The fold case of cofield F in the walk at the motive S -> S: the step
   first, then the rest of the walk. */
static void cocell_walk_case(Text *t, const char *dn, const char *f, CocellField kind) {
  switch (kind) {
  case COCELL_OBSERVATION:
    break;
  case COCELL_COFIELD:
    text_add(t, "\n    (fun (.ih : .S -> .S) (.s : .S) => .ih (.t.%s .s))", f);
    break;
  case COCELL_LABELLED:
    text_add(t, "\n    (fun (.e : %s.%s.E) (.ih : .S -> .S) (.s : .S) => .ih (.t.%s .s .e))", dn, f, f);
    break;
  }
}

static void cocell_walk_arg(Text *t, const char *f, CocellField kind) {
  switch (kind) {
  case COCELL_OBSERVATION:
    break;
  case COCELL_COFIELD:
  case COCELL_LABELLED:
    text_add(t, " .t.%s", f);
    break;
  }
}

/* The bisimulation motive at the position .q. */
static void cocell_motive(Text *t, const char *dn) {
  text_add(t, "(.u : %s .A) -> (.v : %s .A) -> .R .u .v -> Path .A (.u .q) (.v .q)", dn, dn);
}

/* The bisimulation hypothesis of field F, then SUFFIX. */
static void cocell_hyp(Text *t, const char *dn, const char *f, CocellField kind, const char *suffix) {
  text_add(t, "\n    (.h.%s : (.u : %s .A) -> (.v : %s .A) -> .R .u .v -> ", f, dn, dn);
  switch (kind) {
  case COCELL_OBSERVATION:
    text_add(t, "Path .A (%s .A .u) (%s .A .v))%s", f, f, suffix);
    break;
  case COCELL_COFIELD:
    text_add(t, ".R (%s .A .u) (%s .A .v))%s", f, f, suffix);
    break;
  case COCELL_LABELLED:
    text_add(t, "(.e : %s.%s.E) -> .R (%s .A .u .e) (%s .A .v .e))%s", dn, f, f, f, suffix);
    break;
  }
}

/* The elim case of cofield F in the bisimulation: the label, the rest,
   its induction hypothesis, then the two streams and the relation. */
static void cocell_bisim_case(Text *t, const char *dn, const char *f, CocellField kind) {
  switch (kind) {
  case COCELL_OBSERVATION:
    break;
  case COCELL_COFIELD:
    text_add(t, "\n    (fun (.q : %s.pos) (.ih : ", dn);
    cocell_motive(t, dn);
    text_add(t, ") (.u : %s .A) (.v : %s .A) (.w : .R .u .v) => .ih (%s .A .u) (%s .A .v) (.h.%s .u .v .w))", dn, dn, f, f, f);
    break;
  case COCELL_LABELLED:
    text_add(t, "\n    (fun (.e : %s.%s.E) (.q : %s.pos) (.ih : ", dn, f, dn);
    cocell_motive(t, dn);
    text_add(t, ") (.u : %s .A) (.v : %s .A) (.w : .R .u .v) => .ih (%s .A .u .e) (%s .A .v .e) (.h.%s .u .v .w .e))", dn, dn, f, f, f);
    break;
  }
}

/* The elaboration of `cofamily D (A : Type n) := c fields` (S4, choice
   (ii)): the positions D.pos, `D A := D.pos -> A`, one destructor per
   field, the walk, the corecursor c and the bisimulation principle
   DBisim. Generated binders start with `.`, so they never capture a user
   name. */
static void cocell_text(Text *t, const Decl *d, uint64_t n, const CocellField *kinds) {
  const Ctor *ctor = d->ctors;
  const char *dn = d->name;
  const char *obs = "";
  unsigned long long u = (unsigned long long)n;
  size_t j;
  for (j = 0; j < ctor->field_count; j++)
    obs = kinds[j] == COCELL_OBSERVATION ? ctor->fields[j].name : obs;
  text_add(t, "family %s.pos := %s.here", dn, dn);
  for (j = 0; j < ctor->field_count; j++)
    cocell_pos(t, dn, ctor->fields[j].name, kinds[j]);
  text_add(t, "\ndef %s : Type %llu -> Type %llu := fun (.A : Type %llu) => %s.pos -> .A\n", dn, u, u, u, dn);
  for (j = 0; j < ctor->field_count; j++)
    cocell_dtor(t, dn, ctor->fields[j].name, kinds[j], u);
  text_add(t, "def %s.walk : (.S : Type %llu) ->", dn, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_step(t, dn, ctor->fields[j].name, kinds[j], " ->");
  text_add(t, " %s.pos -> .S -> .S :=\n  fun (.S : Type %llu)", dn, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_step(t, dn, ctor->fields[j].name, kinds[j], "");
  text_add(t, " (.p : %s.pos) => fold (fun (.s : .S) => .s)", dn);
  for (j = 0; j < ctor->field_count; j++)
    cocell_walk_case(t, dn, ctor->fields[j].name, kinds[j]);
  text_add(t, " .p\ndef %s : (.A : Type %llu) -> (.S : Type %llu) -> (.o : .S -> .A) ->", ctor->name, u, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_step(t, dn, ctor->fields[j].name, kinds[j], " ->");
  text_add(t, " .S -> %s .A :=\n  fun (.A : Type %llu) (.S : Type %llu) (.o : .S -> .A)", dn, u, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_step(t, dn, ctor->fields[j].name, kinds[j], "");
  text_add(t, " (.seed : .S) (.p : %s.pos) => .o (%s.walk .S", dn, dn);
  for (j = 0; j < ctor->field_count; j++)
    cocell_walk_arg(t, ctor->fields[j].name, kinds[j]);
  text_add(t, " .p .seed)\ndef %sBisim : (.A : Type %llu) -> (.R : %s .A -> %s .A -> Type %llu) ->", dn, u, dn, dn, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_hyp(t, dn, ctor->fields[j].name, kinds[j], " ->");
  text_add(t, "\n    (.x : %s .A) -> (.y : %s .A) -> .R .x .y -> Path (%s .A) .x .y :=\n  fun (.A : Type %llu) (.R : %s .A -> %s .A -> Type %llu)", dn, dn, dn, u, dn, dn, u);
  for (j = 0; j < ctor->field_count; j++)
    cocell_hyp(t, dn, ctor->fields[j].name, kinds[j], "");
  text_add(t, "\n    (.x : %s .A) (.y : %s .A) (.r : .R .x .y) =>\n  funExt (fun (.p : %s.pos) => elim (fun (.q : %s.pos) => ", dn, dn, dn, dn);
  cocell_motive(t, dn);
  text_add(t, ") .h.%s", obs);
  for (j = 0; j < ctor->field_count; j++)
    cocell_bisim_case(t, dn, ctor->fields[j].name, kinds[j]);
  text_add(t, " .p .x .y .r)\n");
}

/* A fresh context for the declaration NAME at INDEX of the list. */
static void checker_reset(Checker *c, size_t index, const char *name) {
  c->decl_index = index;
  c->scope = NULL;
  c->env = NULL;
  c->level = 0;
  c->depth = 0;
  c->self = NO_FAMILY;
  c->self_count = 0u;
  c->fold_targets = NULL;
  c->elim_motive = NULL;
  c->m->def = name;
}

/* A declaration that a cofamily elaborates to: a fresh context, then rule
   R4 on its name (check_def does not check it). */
static int check_generated(Checker *c, const Decl *d) {
  checker_reset(c, c->decl_index, d->name);
  if (!name_free(c, d->name))
    return 0;
  return d->kind == DECL_FAMILY ? check_family(c, d) : check_def(c, d);
}

/* The label type E of the labelled cofield FIELD of D, at the universe K
   of the shape check: `def D.FIELD.E : Type K := E`. BODY is its checked,
   closed normal form, so erased local references cannot escape. */
static int check_label(Checker *c, const Decl *d, const Field *field, uint64_t k, const Core *body) {
  Arena *arena = c->m->arena;
  size_t size = strlen(d->name) + strlen(field->name) + 4u;
  char *name = arena_alloc(arena, size);
  Decl *e = arena_alloc(arena, sizeof *e);
  if (name == NULL || e == NULL)
    return FAIL(c, "OOM", "out of memory");
  snprintf(name, size, "%s.%s.E", d->name, field->name);
  memset(e, 0, sizeof *e);
  e->kind = DECL_DEF;
  e->origin = ORIGIN_DOMAIN;
  e->line = field->line;
  e->col = field->col;
  e->name = name;
  e->block_count = 1u;
  checker_reset(c, c->decl_index, name);
  return name_free(c, name) && check_def_body(c, e, val_univ(c->m, k), NULL, body);
}

/* A cofamily (S4, rule R1): the shape check, then the label types, then
   the generated text, lexed with `.` as a name character and checked
   declaration by declaration. */
static int check_cofamily(Checker *c, const Decl *d) {
  Machine *m = c->m;
  size_t count = d->ctor_count == 1u ? d->ctors[0].field_count : 0u;
  size_t size = strlen(d->name) + 10u;
  CocellField *kinds = arena_alloc(m->arena, (count + 1u) * sizeof *kinds);
  uint64_t *labels = arena_alloc(m->arena, (count + 1u) * sizeof *labels);
  const Core **label_types = arena_alloc(m->arena, (count + 1u) * sizeof *label_types);
  char *source = arena_alloc(m->arena, size);
  Text t = {NULL, 0, 0};
  TokenList toks = {0};
  DeclList list = {NULL, 0, 0};
  uint64_t n = 0;
  size_t i;
  if (kinds == NULL || labels == NULL || label_types == NULL || source == NULL)
    return FAIL(c, "OOM", "out of memory");
  if (!cocell_shape(c, d, &n, kinds, labels, label_types))
    return 0;
  snprintf(source, size, "cofamily %s", d->name);
  cocell_text(&t, d, n, kinds);
  t.cap = t.len + 1u;
  t.len = 0;
  t.text = arena_alloc(m->arena, t.cap);
  if (t.text == NULL)
    return FAIL(c, "OOM", "out of memory");
  cocell_text(&t, d, n, kinds);
  for (i = 0; i < count; i++)
    if (kinds[i] == COCELL_LABELLED && !check_label(c, d, &d->ctors[0].fields[i], labels[i], label_types[i]))
      return 0;
  if (!lex_internal(m->arena, source, t.text, t.len, &toks, m->diag) || !parse_source(m->arena, source, ORIGIN_DOMAIN, &toks, &list, m->diag))
    return 0;
  for (i = 0; i < list.count; i++)
    if (!check_generated(c, &list.items[i]))
      return 0;
  return 1;
}

/* Q-S5-12 (a): a footprint clause (X17) goes only on a family of one sort
   with one constructor and no `: result`. The checker refuses a footprint
   on the state form, on a cofamily, on a sort of an `and` block, on a
   family with more than one constructor and on a constructor with
   `: result`. D is the first sort of its block. */
static int footprint_shape(Checker *c, const Decl *d) {
  size_t count = d->block_count > 0u ? d->block_count : 1u;
  size_t s;
  for (s = 0; s < count; s++) {
    const Decl *e = &d[s];
    if (e->footprint == NULL)
      continue;
    if (e->is_state)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s is the state form with a footprint clause; a footprint clause goes on a family (Q-S5-12 (a))", e->name);
    if (e->kind == DECL_COFAMILY)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s is a cofamily with a footprint clause; a footprint clause goes on a family (Q-S5-12 (a))", e->name);
    if (count > 1u)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s is a sort of an and block with a footprint clause; a footprint family is a block of one sort (Q-S5-12 (a))", e->name);
    if (e->param_count > 0u)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s has %zu parameters and a footprint clause; a footprint family has no parameters, as a Body summand is a closed type (Q-S5-17 (a), Q-S5-6 (a))", e->name, e->param_count);
    if (e->ctor_count != 1u)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s has %zu constructors; a footprint family has one constructor (Q-S5-12 (a))", e->name, e->ctor_count);
    if (e->ctors[0].result != NULL)
      return FAIL(c, "REFUSE_FOOTPRINT_SHAPE", "%s has a footprint clause and its constructor %s has a result `: F ...`; a footprint family is not indexed (Q-S5-12 (a))", e->name, e->ctors[0].name);
  }
  return 1;
}

/* The index of the key space NAME in the key space table, or
   m->space_count when no key space has that name. */
static size_t find_space(const Machine *m, const char *name) {
  size_t i;
  for (i = 0; i < m->space_count; i++) {
    if (strcmp(m->spaces[i].name, name) == 0)
      return i;
  }
  return m->space_count;
}

/* Q-S5-15 (a) (u4g): the type FOUND of the footprint pattern argument WHAT
   is the key space argument type WANT. TYPE_MISMATCH on a miss. */
static int footprint_arg_type(Checker *c, const Decl *d, const KeyPat *kp, const Value *found, const Value *want, const char *what) {
  if (found != NULL && want != NULL && conv_values(c->m, c->level, found, want))
    return 1;
  return FAIL(c, "TYPE_MISMATCH", "the argument %s of the pattern %s in the footprint of %s has the type %s; the key space %s wants %s at its position (Q-S5-15 (a))", what, kp->space, d->name, found != NULL ? show(c, found) : "?", kp->space, want != NULL ? show(c, want) : "?");
}

/* Q-S5-15 (a), Q-S5-17 (a) (u4g): the type of the field J of CI. A
   footprint family has no parameters (footprint_shape), so a field type
   that uses no earlier field is closed: eval it in the empty env. A field
   type that uses an earlier field is not a closed key argument type. */
static int footprint_field_type(Checker *c, const Decl *d, const CtorInfo *ci, const KeyPat *kp, uint32_t j, const Value *want) {
  const FieldInfo *fi = &ci->fields[j];
  if (fi->dependent || fi->over_recursive || fi->path)
    return FAIL(c, "TYPE_MISMATCH", "the argument %s.%s of the pattern %s in the footprint of %s: the type of the field %s uses an earlier field, so it is not a closed key argument type (Q-S5-17 (a))", d->footprint->binder, fi->name, kp->space, d->name, fi->name);
  return footprint_arg_type(c, d, kp, eval_core(c->m, NULL, fi->type), want, fi->name);
}

/* u4 item 5 (X17, survey sec 1): an argument of a footprint pattern is
   static. A numeral fits. A name is a closed def (find_def). `b.field`
   projects the binder b to a field of the one constructor CI of the
   family (the proj_app lookup). Q-S5-15 (a) (u4g): the argument has
   the key space argument type WANT at its position (TYPE_MISMATCH). */
static int footprint_arg(Checker *c, const Decl *d, const CtorInfo *ci, const KeyPat *kp, const PatArg *pa, const Value *want) {
  uint32_t j;
  uint32_t def = NO_DEF;
  switch (pa->kind) {
  case PAT_ARG_NAT:
    return footprint_arg_type(c, d, kp, nat_type(c), want, "a numeral");
  case PAT_ARG_NAME:
    def = pa->name != NULL ? find_def(c->m, pa->name) : NO_DEF;
    if (def != NO_DEF)
      return footprint_arg_type(c, d, kp, c->m->defs[def].type, want, pa->name);
    return FAIL(c, "REFUSE_FOOTPRINT_DYNAMIC", "the argument %s of the pattern %s in the footprint of %s is not a closed def; an argument is b.field, a numeral or a closed def (X17)", pa->name != NULL ? pa->name : "?", kp->space, d->name);
  case PAT_ARG_FIELD:
    break;
  }
  if (pa->base == NULL || pa->name == NULL || strcmp(pa->base, d->footprint->binder) != 0)
    return FAIL(c, "REFUSE_FOOTPRINT_DYNAMIC", "the argument %s.%s of the pattern %s in the footprint of %s does not project the binder %s; an argument is b.field, a numeral or a closed def (X17)", pa->base != NULL ? pa->base : "?", pa->name != NULL ? pa->name : "?", kp->space, d->name, d->footprint->binder);
  for (j = 0; j < ci->field_count; j++) {
    if (ci->fields[j].name != NULL && strcmp(ci->fields[j].name, pa->name) == 0)
      return footprint_field_type(c, d, ci, kp, j, want);
  }
  return FAIL(c, "REFUSE_FOOTPRINT_DYNAMIC", "the argument %s.%s of the pattern %s in the footprint of %s: the constructor %s has no field %s (X17)", pa->base, pa->name, kp->space, d->name, ci->name, pa->name);
}

/* u4 item 5: each pattern of a footprint clause names a key space of the
   key space table and has its arity (Q-S5-16 (a): NAME_UNKNOWN for a
   space that is not declared, REFUSE_KEYSPACE for a wrong count). Each
   argument is static (footprint_arg). */
static int footprint_pats(Checker *c, const Decl *d, const CtorInfo *ci, const KeyPat *pats, size_t n) {
  const Machine *m = c->m;
  size_t p;
  size_t a;
  for (p = 0; p < n; p++) {
    size_t s = find_space(m, pats[p].space);
    if (s == m->space_count)
      return FAIL(c, "NAME_UNKNOWN", "the pattern %s in the footprint of %s names no key space; declare keyspace %s before the family (Q-S5-16 (a))", pats[p].space, d->name, pats[p].space);
    if (pats[p].arg_count != m->spaces[s].arity)
      return FAIL(c, "REFUSE_KEYSPACE", "the pattern %s in the footprint of %s has %zu arguments; the key space %s has the arity %u (Q-S5-13 (a), Q-S5-16 (a))", pats[p].space, d->name, pats[p].arg_count, pats[p].space, (unsigned)m->spaces[s].arity);
    for (a = 0; a < pats[p].arg_count; a++) {
      if (!footprint_arg(c, d, ci, &pats[p], &pats[p].args[a], m->spaces[s].arg_types[a]))
        return 0;
    }
  }
  return 1;
}

/* u4 item 5 (X17): the footprint clause of the family D, after
   check_family. The family is the last one with its name in the family
   table. footprint_shape gives it one constructor. */
/* Law L5 at step (S5 survey section 4, USER ruling Q-S4-2 (a)). 1 if a
   parameter type or a point field type of the family FAM mentions
   Witness, Authorized or AuthTx, also through the body of a program def
   (an alias). A footprint family is a summand of Body, so it passes the
   S4 Body slot rule. */
static int family_mentions_witness(const Machine *m, uint32_t fam) {
  uint32_t i, j;
  for (i = 0; i < m->families[fam].param_count; i++) {
    if (mentions_witness(m, m->families[fam].param_types[i]))
      return 1;
  }
  for (j = 0; j < m->families[fam].ctor_count; j++) {
    const CtorInfo *ci = &m->ctors[m->families[fam].first_ctor + j];
    for (i = 0; i < ci->field_count; i++) {
      if (mentions_witness(m, ci->fields[i].type))
        return 1;
    }
  }
  return 0;
}

static int footprint_decl(Checker *c, const Decl *d) {
  const Machine *m = c->m;
  const CtorInfo *ci = NULL;
  uint32_t i;
  if (d->footprint == NULL)
    return 1;
  /* Q-S5-19 (a): check_sig checks only a def, so a footprint family with
     a slot or program name would skip the slot rules and the kernel-fixed
     types. A footprint family is a summand of Body, not a slot. */
  if (sig_row(d->name) != SIG_COUNT)
    return FAIL(c, "REFUSE_SIG", "the footprint family %s has a name of the design signature: a footprint family is a summand of Body, not a slot or a program name (Q-S5-19 (a))", d->name);
  for (i = 0; i < m->family_count; i++) {
    if (m->families[i].name != NULL && strcmp(m->families[i].name, d->name) == 0)
      ci = &m->ctors[m->families[i].first_ctor];
  }
  if (ci == NULL)
    return FAIL(c, "INTERNAL", "the footprint family %s is not in the family table", d->name);
  /* Law L5 at step (S5 survey section 4, USER ruling Q-S4-2 (a)). */
  if (family_mentions_witness(m, ci->family))
    return FAIL(c, "REFUSE_WITNESS_READ", "the footprint family %s must not mention Witness, Authorized or AuthTx: a footprint family is a summand of Body, and txid and step read the body only (law L5, PLAN section 6, USER ruling Q-S4-2 (a), S5 survey section 4)", d->name);
  return footprint_pats(c, d, ci, d->footprint->reads, d->footprint->read_count) && footprint_pats(c, d, ci, d->footprint->writes, d->footprint->write_count);
}

/* Q-S5-14 (a): a key argument type is a first-order type, the base name
   Size (the domain family), or Option, Prod and List of key argument
   types. first_order does not change: the state and slot rules use it. */
static int key_arg_type(const Machine *m, const Value *t) {
  uint32_t i;
  if (first_order(t))
    return 1;
  if (t == NULL || t->kind != VAL_OP)
    return 0;
  if (t->op == OP_FAMILY)
    return t->argc == 0u && t->inst < m->family_count && m->families[t->inst].name != NULL && strcmp(m->families[t->inst].name, "Size") == 0;
  if (t->op != OP_OPTION && t->op != OP_PROD && t->op != OP_LIST)
    return 0;
  for (i = 0; i < t->argc; i++) {
    if (!key_arg_type(m, t->args[i]))
      return 0;
  }
  return 1;
}

/* Q-S5-25 (a): 1 if the term T of a key argument type is written in one
   of the six forms that keyEq has an eq term for: the name Nat, Size or
   Flag, `Option T` or `List T`, or `Prod A B`, with each T, A and B again
   one of the six forms. An alias def name, Unit, Sum, Fin, a program
   family and a Pi are not. front.c has the same test for the key-eq
   prelude. */
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

/* Q-S5-13 (a): a key space `Space : A1 -> ... -> An -> Key` (X17) has
   n >= 1 arguments, each of a key argument type (key_arg_type,
   Q-S5-14 (a)), and the codomain Key, the generated family of the key
   spaces (Q-S5-23 (a)). The space has no body. The pattern arity is n.
   The space goes in the key space table (name, arity and the argument
   types, Q-S5-15 (a)) for the pattern
   checks of a footprint (u4 item 5). */
static int check_keyspace(Checker *c, const Decl *d) {
  Machine *m = c->m;
  const Term *t = d->type;
  size_t arity = 0;
  size_t n = 0;
  uint64_t level = 0;
  const Value **types;
  for (; t != NULL && t->kind == TERM_PI; t = t->right)
    n++;
  types = arena_alloc(m->arena, (n + 1u) * sizeof *types);
  if (types == NULL)
    return FAIL(c, "OOM", "out of memory");
  for (t = d->type; t != NULL && t->kind == TERM_PI; t = t->right) {
    uint64_t arg_level = 0;
    const Core *a = check_type(c, t->left, &arg_level);
    const Value *av = a == NULL ? NULL : here(c, a);
    if (a == NULL)
      return 0;
    types[arity] = av;
    if (!key_arg_type(m, av))
      return FAIL(c, "REFUSE_KEYSPACE", "argument %zu of the key space %s does not have a key argument type (Nat, Flag, the base name Size, or Option, Prod and List of them); Q-S5-13 (a) and Q-S5-14 (a)", arity + 1u, d->name);
    if (!key_arg_form(t->left))
      return FAIL(c, "REFUSE_KEYSPACE", "argument %zu of the key space %s is not written as Nat, Size, Flag, Option T, List T or Prod A B (each T, A and B again one of these forms), so keyEq has no eq term for it (Q-S5-25 (a))", arity + 1u, d->name);
    arity++;
  }
  if (arity == 0u)
    return FAIL(c, "REFUSE_KEYSPACE", "the key space %s has no argument; its type is A1 -> ... -> An -> Key with n >= 1 (Q-S5-13 (a))", d->name);
  if (t == NULL || t->kind != TERM_VAR || t->name == NULL || strcmp(t->name, "Key") != 0)
    return FAIL(c, "REFUSE_KEYSPACE", "the codomain of the key space %s is not Key, the generated family of the key spaces (Q-S5-13 (a), Q-S5-23 (a))", d->name);
  if (check_type(c, d->type, &level) == NULL)
    return 0;
  if (m->space_count >= m->space_cap)
    return FAIL(c, "OOM", "the key space table is full");
  m->spaces[m->space_count].name = d->name;
  m->spaces[m->space_count].arity = (uint32_t)arity;
  m->spaces[m->space_count].arg_types = types;
  m->space_count++;
  return 1;
}

/* Q-S5-21 (a): 1 if NAME is bound by a get or a let item before the item N
   of the step S. */
static int step_bound(const StepDecl *s, size_t n, const char *name) {
  size_t i;
  for (i = 0; i < n && !(s->items[i].kind != STEP_SET && s->items[i].name != NULL && name != NULL && strcmp(s->items[i].name, name) == 0); i++)
    ;
  return i < n;
}

/* Q-S5-21 (a): each argument of a step pattern is static. A name bound by
   an earlier get or let item, and a field whose base is not the step
   binder, give REFUSE_FOOTPRINT_DYNAMIC. The item N is the pattern item. */
static int step_args_static(Checker *c, const Decl *d, size_t n, const KeyPat *kp) {
  const StepDecl *s = d->step;
  size_t a;
  for (a = 0; a < kp->arg_count; a++) {
    const PatArg *pa = &kp->args[a];
    if (pa->kind == PAT_ARG_NAME && step_bound(s, n, pa->name))
      return FAIL(c, "REFUSE_FOOTPRINT_DYNAMIC", "the argument %s of the pattern %s in the step of %s is a name of a get or a let of the step; a step pattern is static (X17, Q-S5-21 (a))", pa->name, kp->space, d->name);
    if (pa->kind == PAT_ARG_FIELD && (pa->base == NULL || strcmp(pa->base, s->binder) != 0))
      return FAIL(c, "REFUSE_FOOTPRINT_DYNAMIC", "the argument %s.%s of the pattern %s in the step of %s does not project the step binder %s; a step pattern is static (X17, Q-S5-21 (a))", pa->base != NULL ? pa->base : "?", pa->name != NULL ? pa->name : "?", kp->space, d->name, s->binder);
  }
  return 1;
}

/* 1 if the step argument SA is the footprint argument FA. The step binder
   is renamed to the footprint binder (PLAN 5.2): step_args_static checked
   the step base, footprint_arg the footprint base, so a field compares by
   its field name. */
static int step_arg_same(const PatArg *sa, const PatArg *fa) {
  if (sa->kind != fa->kind)
    return 0;
  switch (sa->kind) {
  case PAT_ARG_NAT:
    return sa->nat == fa->nat;
  case PAT_ARG_NAME:
  case PAT_ARG_FIELD:
    return sa->name != NULL && fa->name != NULL && strcmp(sa->name, fa->name) == 0;
  }
  return 0;
}

/* 1 if the step pattern KP is one of the N footprint patterns PATS. */
static int step_pat_in(const KeyPat *kp, const KeyPat *pats, size_t n) {
  size_t p;
  size_t a;
  for (p = 0; p < n; p++) {
    if (kp->space == NULL || pats[p].space == NULL || strcmp(kp->space, pats[p].space) != 0 || kp->arg_count != pats[p].arg_count)
      continue;
    for (a = 0; a < kp->arg_count && step_arg_same(&kp->args[a], &pats[p].args[a]); a++)
      ;
    if (a == kp->arg_count)
      return 1;
  }
  return 0;
}

/* The type value of the global NAME for the step terms (S5 u4k): the
   name elaborated as a type in the empty context, before the step binds
   a local. NAME is Val or the footprint family of the step. */
static const Value *step_type(Checker *c, const char *name, const StepDecl *s) {
  Term v;
  uint64_t level = 0;
  const Core *k;
  memset(&v, 0, sizeof v);
  v.kind = TERM_VAR;
  v.name = name;
  v.line = s->item_count > 0 ? s->items[0].line : 0;
  v.col = s->item_count > 0 ? s->items[0].col : 0;
  k = check_type(c, &v, &level);
  return k == NULL ? NULL : here(c, k);
}

/* u4 item 7 (Q-S5-10 (a), Q-S5-20 (a), Q-S5-21 (a)), unit u4j: the
   pattern rules of `step Fam b := [item, ...]`. Fam is the last earlier
   program family of the name (else NAME_UNKNOWN) and has a footprint
   (else REFUSE_STEP; a program family without a footprint is REFUSE_DATA
   first, so this is a guard). A second step of Fam is REFUSE_STEP. The
   binder b is renamed to the footprint binder. One pass with the phase
   read, decide, write; it starts at read. A get pattern comes before the
   first set (REFUSE_FOOTPRINT_PHASE) and is in reads
   (REFUSE_FOOTPRINT_READ). A set pattern is in writes
   (REFUSE_FOOTPRINT_WRITE) and moves the phase to write. The step decl
   name is the family name: no name_free. Unit u4k checks the terms (the
   let and set values, x : Val for a get, the let phase rule). */
/* Q-S5-26 (a), Q-S5-27 (a): infer a bare `fun y => t` (no binder type)
   with y at DOM, the type that the first argument of bind or step#let
   gives. */
static const Core *infer_bare_lam(Checker *c, const Term *t, const Value *dom, const Value **type) {
  const Value *bt = NULL;
  const Core *ann = quote_value(c->m, c->level, dom);
  const Core *body;
  const Core *quoted;
  if (!push(c, t->name, dom))
    return NULL;
  body = infer(c, t->right, &bt);
  quoted = body == NULL || bt == NULL ? NULL : quote_value(c->m, c->level, bt);
  pop(c);
  if (body == NULL)
    return NULL;
  if (quoted == NULL)
    return nul(FAIL(c, "INTERNAL", "the body of fun %s => ... has no type", t->name));
  *type = val_closure(c->m, VAL_PI, t->name, dom, c->env, quoted);
  return core_bind(c, CORE_LAM, t->name, ann, body);
}

/* The fn_into of a bare lambda (Q-S5-26 (a)): RESULT is the body type. The
   body type must not use the binder. */
static const Core *bare_fn_into(Checker *c, const Term *t, const Value *dom, const Value **result) {
  const Value *ft = NULL;
  const Core *f = infer_bare_lam(c, t, dom, &ft);
  if (f == NULL)
    return NULL;
  *result = closure_apply(c->m, ft, val_var(c->m, c->level));
  if (!conv_values(c->m, c->level + 2u, *result,
                   closure_apply(c->m, ft, val_var(c->m, c->level + 1u))))
    return nul(FAIL(c, "TYPE_MISMATCH", "this operation needs a function with a non-dependent result type"));
  return f;
}

/* Q-S5-27 (a): `step#let e (fun y => t)`, the step let that the front
   writes (the lexer cannot make the name). At `Maybe T` it is the bind rule
   with y : T. Else it is the bare lambda with y at the type of e, applied
   to e (the step_check let rule). */
static const Core *rule_step_let(Call *k) {
  Checker *c = k->c;
  const Value *ty = NULL;
  const Value *ft = NULL;
  const Core *x;
  const Core *f;
  if (!is_bare_lam(k->args[1]))
    return nul(FAIL(c, "INTERNAL", "step#let needs a bare lambda as its second argument"));
  x = infer(c, k->args[0], &ty);
  if (x == NULL)
    return NULL;
  if (ty == NULL)
    return nul(FAIL(c, "INTERNAL", "the let value of %s has no type", k->args[1]->name));
  if (val_is(ty, OP_OPTION))
    return rule_bind(k);
  f = infer_bare_lam(c, k->args[1], ty, &ft);
  if (f == NULL)
    return NULL;
  k->type = closure_apply(c->m, ft, here(c, x));
  return core_app(c, f, x);
}

static int step_check(Checker *c, const Decl *d) {
  const DeclList *ds = c->decls;
  const Decl *fam = NULL;
  const StepDecl *s = d->step;
  size_t at;
  size_t i;
  int phase_write = 0;
  int ok;
  size_t pushed;
  const Value *val_ty;
  const Value *fam_ty;
  for (at = 0; at < ds->count && &ds->items[at] != d; at++)
    ;
  if (at == ds->count || s == NULL || d->name == NULL || s->binder == NULL)
    return FAIL(c, "INTERNAL", "the step is not in the declaration list or has no name");
  for (i = 0; i < at; i++) {
    if (ds->items[i].kind == DECL_FAMILY && ds->items[i].origin == ORIGIN_PROGRAM && ds->items[i].name != NULL && strcmp(ds->items[i].name, d->name) == 0)
      fam = &ds->items[i];
  }
  if (fam == NULL)
    return FAIL(c, "NAME_UNKNOWN", "the step names %s, but no program family %s comes before it (Q-S5-20 (a))", d->name, d->name);
  if (fam->footprint == NULL)
    return FAIL(c, "REFUSE_STEP", "the family %s has no footprint clause; a step is for a footprint family (Q-S5-10 (a), Q-S5-20 (a))", d->name);
  for (i = 0; i < at; i++) {
    if (ds->items[i].kind == DECL_STEP && ds->items[i].name != NULL && strcmp(ds->items[i].name, d->name) == 0)
      return FAIL(c, "REFUSE_STEP", "the family %s has a second step; a family has one step (Q-S5-20 (a))", d->name);
  }
  val_ty = step_type(c, "Val", s);
  fam_ty = val_ty == NULL ? NULL : step_type(c, d->name, s);
  ok = fam_ty != NULL && push(c, s->binder, fam_ty);
  pushed = ok ? 1u : 0u;
  for (i = 0; ok && i < s->item_count; i++) {
    const StepItem *it = &s->items[i];
    const Value *ty = NULL;
    switch (it->kind) {
    case STEP_GET:
      ok = step_args_static(c, d, i, &it->pat);
      if (ok && phase_write)
        ok = FAIL(c, "REFUSE_FOOTPRINT_PHASE", "the get of %s in the step of %s comes after a set; the phase is read, decide, write (X17)", it->pat.space, d->name);
      if (ok && !step_pat_in(&it->pat, fam->footprint->reads, fam->footprint->read_count))
        ok = FAIL(c, "REFUSE_FOOTPRINT_READ", "the get pattern %s in the step of %s is not in the reads of its footprint (X17)", it->pat.space, d->name);
      ok = ok && push(c, it->name, val_ty);
      pushed += ok ? 1u : 0u;
      break;
    case STEP_SET:
      ok = step_args_static(c, d, i, &it->pat);
      if (ok && !step_pat_in(&it->pat, fam->footprint->writes, fam->footprint->write_count))
        ok = FAIL(c, "REFUSE_FOOTPRINT_WRITE", "the set pattern %s in the step of %s is not in the writes of its footprint (X17)", it->pat.space, d->name);
      ok = ok && check(c, it->term, val_ty) != NULL;
      phase_write = 1;
      break;
    case STEP_LET:
      ok = infer(c, it->term, &ty) != NULL;
      if (ok && ty == NULL)
        ok = FAIL(c, "INTERNAL", "the let value of %s in the step of %s has no type", it->name, d->name);
      if (ok && phase_write && val_is(ty, OP_OPTION))
        ok = FAIL(c, "REFUSE_FOOTPRINT_PHASE", "the let of %s in the step of %s has a Maybe type and comes after a set; a let that can give none is not in the write phase (X17, Q-S5-4 (a))", it->name, d->name);
      ok = ok && push(c, it->name, val_is(ty, OP_OPTION) ? ty->args[0] : ty);
      pushed += ok ? 1u : 0u;
      break;
    }
  }
  for (; pushed > 0u; pushed--)
    pop(c);
  return ok;
}

static int check_decl(Checker *c, const Decl *d) {
  const DroppedName *x = d->name != NULL ? dropped_name(d->name) : NULL;
  if (x != NULL)
    return FAIL(c, "REFUSE_NOT_IN_DESIGN", DROPPED_HINT, d->name, x->row, x->why);
  if (d->kind == DECL_AXIOM && d->name != NULL && d->type != NULL && d->type->kind == TERM_UNIV && !admitted_name(d->name))
    return FAIL(c, "REFUSE_NOT_IN_DESIGN", "%s is not a base sort of PLAN section 4 (X1 to X21, the design parameters, the section 3 instances); a base sort comes from the design only", d->name);
  if (!footprint_shape(c, d))
    return 0;
  if (d->is_state && guest(c))
    return kit_refused(c, "the state form");
  if (d->is_state)
    return check_state(c, d);
  /* Q-S5-11 (a): a program can declare a family that has a footprint
     clause (X17); the other program families stay refused (rule R1). */
  if (d->kind == DECL_FAMILY && d->origin == ORIGIN_PROGRAM && d->footprint == NULL)
    return FAIL(c, "REFUSE_DATA", "a program cannot declare a family (rule R1); only domain/domain.lang can");
  if (d->kind == DECL_COFAMILY && d->origin == ORIGIN_PROGRAM)
    return FAIL(c, "REFUSE_DATA", "a program cannot declare a cofamily (rule R1); only domain/domain.lang can");
  if (d->is_law && d->origin == ORIGIN_PROGRAM)
    return FAIL(c, "REFUSE_DATA", "a program cannot declare a law def (rule O7); only domain/domain.lang can");
  if (d->kind == DECL_AXIOM)
    return FAIL(c, "REFUSE_AXIOM", "an axiom has no proof (rule R2)");
  if (d->is_rec)
    return FAIL(c, "REFUSE_REC", "def rec is refused (rule R3); use fold or unfold");
  /* u4 item 7 (Q-S5-10 (a)): a step has no type, and its name is the
     family name, so step_check comes before kernel_sig and name_free. */
  if (d->kind == DECL_STEP)
    return step_check(c, d);
  /* Q-S5-24 (a): a key space name is the name of its constructor in the
     generated family Key, so the family check covers its name clashes. */
  if (!kernel_sig(c, d) || (d->kind != DECL_KEYSPACE && !name_free(c, d->name)))
    return 0;
  switch (d->kind) {
  case DECL_FAMILY:
    return check_family(c, d) && footprint_decl(c, d);
  case DECL_COFAMILY:
    return check_cofamily(c, d);
  case DECL_KEYSPACE:
    return check_keyspace(c, d);
  case DECL_STEP:
    return step_check(c, d);
  case DECL_DEF:
  case DECL_AXIOM:
    break;
  }
  return check_def(c, d);
}

/* The Ind matrix (S5 unit 5, X2, survey secs 5 and 6, PLAN 5.4). One row
   for each pair a <= b of the program footprint families in declaration
   order, a = b included. The conflict pairs of a row are writes a x (reads
   b + writes b) and reads a x writes b: shared reads are allowed. Two key
   patterns of different spaces do not meet. At one position, two constants
   that are not equal do not meet (Q-S5-33 (a): by value, with
   conv_values); each other position gives the literal `x != y`. A pattern
   pair that can meet gives one clause (the OR of its literals). An empty
   clause gives dep; no clause gives ind; else ind-if (the AND of the
   clauses). The key equality is static unification, so the verdict is
   exact. L3 is by shape (Q-S5-5 (a)): this matrix and the three-phase step
   check are the evidence. */

/* A new zeroed row at the end of the matrix: the arena array starts at 4
   rows and doubles (the merge-lang machine_row form). */
static IndRow *ind_row(Machine *m) {
  IndMatrix *x = &m->ind;
  IndRow *rows = x->rows;
  if (x->row_count == x->row_cap) {
    uint32_t cap = x->row_cap == 0u ? 4u : 2u * x->row_cap;
    rows = arena_alloc(m->arena, (size_t)cap * sizeof *rows);
    if (rows == NULL)
      return NULL;
    if (x->row_count > 0u)
      memcpy(rows, x->rows, (size_t)x->row_count * sizeof *rows);
    x->rows = rows;
    x->row_cap = cap;
  }
  memset(&rows[x->row_count], 0, sizeof rows[x->row_count]);
  x->row_count++;
  return &rows[x->row_count - 1u];
}

/* A footprint family of the program (a Body summand). */
static int ind_family(const Decl *d) {
  return d->kind == DECL_FAMILY && d->origin == ORIGIN_PROGRAM && d->footprint != NULL;
}

/* The value of a constant pattern argument: a numeral, or the value of the
   closed def (Q-S5-33 (a)). NULL when it is not known. */
static const Value *ind_const_value(Checker *c, const PatArg *pa) {
  if (pa->kind == PAT_ARG_NAT)
    return val_nat(c->m, pa->nat);
  return pa->name != NULL ? sig_name_value(c, pa->name) : NULL;
}

/* 1 when two constant arguments can be the same value. A value that is not
   known can be the same (the sound default). */
static int ind_const_same(Checker *c, const PatArg *x, const PatArg *y) {
  const Value *vx;
  const Value *vy;
  if (x->kind == PAT_ARG_NAT && y->kind == PAT_ARG_NAT)
    return x->nat == y->nat;
  vx = ind_const_value(c, x);
  vy = ind_const_value(c, y);
  return vx == NULL || vy == NULL || conv_values(c->m, c->level, vx, vy);
}

/* The operand of a pattern argument: a field of the left family
   (IND_OPD_FIELD_A), of the right family (IND_OPD_FIELD_B), or a constant. */
static IndOperand ind_operand(const PatArg *pa, IndOpdKind field) {
  IndOperand o;
  o.kind = pa->kind == PAT_ARG_FIELD ? field : IND_OPD_CONST;
  o.name = pa->kind == PAT_ARG_NAT ? NULL : pa->name;
  o.nat = pa->kind == PAT_ARG_NAT ? pa->nat : 0u;
  return o;
}

/* The clause of the pattern pair KA (left family) and KB (right family),
   put at CLAUSES[*N] when the two keys can meet. An empty clause sets the
   dep space of ROW. */
static int ind_meet(Checker *c, const KeyPat *ka, const KeyPat *kb, IndClause *clauses, uint32_t *n, IndRow *row) {
  IndLit *lits;
  uint32_t k = 0;
  size_t i;
  if (strcmp(ka->space, kb->space) != 0 || ka->arg_count != kb->arg_count)
    return 1;
  for (i = 0; i < ka->arg_count; i++) {
    const PatArg *x = &ka->args[i];
    const PatArg *y = &kb->args[i];
    if (x->kind != PAT_ARG_FIELD && y->kind != PAT_ARG_FIELD && !ind_const_same(c, x, y))
      return 1;
  }
  lits = arena_alloc(c->m->arena, (ka->arg_count + 1u) * sizeof *lits);
  if (lits == NULL)
    return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
  for (i = 0; i < ka->arg_count; i++) {
    const PatArg *x = &ka->args[i];
    const PatArg *y = &kb->args[i];
    if (x->kind == PAT_ARG_FIELD || y->kind == PAT_ARG_FIELD) {
      lits[k].left = ind_operand(x, IND_OPD_FIELD_A);
      lits[k].right = ind_operand(y, IND_OPD_FIELD_B);
      k++;
    }
  }
  if (k == 0u && row->dep_space == NULL)
    row->dep_space = ka->space;
  clauses[*n].lits = lits;
  clauses[*n].lit_count = k;
  clauses[*n].ka = ka;
  clauses[*n].kb = kb;
  (*n)++;
  return 1;
}

/* The row of the footprint families DA <= DB. */
static int ind_pair(Checker *c, const Decl *da, const Decl *db) {
  const FootprintDecl *fa = da->footprint;
  const FootprintDecl *fb = db->footprint;
  size_t cap = fa->write_count * (fb->read_count + fb->write_count) + fa->read_count * fb->write_count;
  IndRow *row = ind_row(c->m);
  IndClause *clauses = arena_alloc(c->m->arena, (cap + 1u) * sizeof *clauses);
  uint32_t n = 0;
  size_t p;
  size_t q;
  if (row == NULL || clauses == NULL)
    return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
  row->a = da->name;
  row->b = db->name;
  row->clauses = clauses;
  for (p = 0; p < fa->write_count; p++) {
    for (q = 0; q < fb->read_count + fb->write_count; q++) {
      const KeyPat *kb = q < fb->read_count ? &fb->reads[q] : &fb->writes[q - fb->read_count];
      if (!ind_meet(c, &fa->writes[p], kb, clauses, &n, row))
        return 0;
    }
  }
  for (p = 0; p < fa->read_count; p++) {
    for (q = 0; q < fb->write_count; q++) {
      if (!ind_meet(c, &fa->reads[p], &fb->writes[q], clauses, &n, row))
        return 0;
    }
  }
  row->clause_count = n;
  row->verdict = row->dep_space != NULL ? IND_DEP : n == 0u ? IND_ALWAYS : IND_IF;
  return 1;
}

/* The Ind matrix of the program, after all the decls check (S5 unit 5). */
static int ind_matrix(Checker *c) {
  const DeclList *decls = c->decls;
  size_t i;
  size_t j;
  for (i = 0; i < decls->count; i++) {
    if (!ind_family(&decls->items[i]))
      continue;
    c->m->ind.body_count++;
    for (j = i; j < decls->count; j++) {
      if (ind_family(&decls->items[j]) && !ind_pair(c, &decls->items[i], &decls->items[j]))
        return 0;
    }
  }
  return 1;
}

/* The placeholder def ind of front.c (USER ruling Q-S6-11 (a)). */
static int ind_site(const Decl *d) {
  return d->kind == DECL_DEF && d->origin == ORIGIN_DOMAIN && d->body == NULL && d->name != NULL && strcmp(d->name, "ind") == 0;
}

/* The def ind at its placeholder (quotient-lang S6, USER ruling Q-S6-11
   (a)). The footprint families are earlier and are checked, so the Ind
   matrix is made here (not after all the decls). The body comes from the
   matrix (front_ind_body) and the def checks as a normal def. */
static int check_ind(Checker *c, const Decl *d) {
  Decl *def = arena_alloc(c->m->arena, sizeof *def);
  if (def == NULL)
    return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
  if (!ind_matrix(c))
    return 0;
  c->m->ind.built = 1u;
  *def = *d;
  def->body = front_ind_body(c->m->arena, c->decls, &c->m->ind, d->line, d->col);
  if (def->body == NULL)
    return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
  return check_decl(c, def);
}

/* A generated def of front.c body_commute whose name has PREFIX
   (com#leaf or com#slot, USER ruling Q-S6-12 (b)). */
static int commute_site(const Decl *d, const char *prefix) {
  return d->kind == DECL_DEF && d->origin == ORIGIN_DOMAIN && d->name != NULL && strncmp(d->name, prefix, strlen(prefix)) == 0;
}

/* The name of the K-th Pi domain of T (the family F or G of a commute
   leaf), or "?" when T has another form. */
static const char *pi_dom(const Term *t, unsigned k) {
  if (t == NULL || t->kind != TERM_PI)
    return "?";
  if (k > 0u)
    return pi_dom(t->right, k - 1u);
  return t->left != NULL && t->left->kind == TERM_VAR ? t->left->name : "?";
}

/* 1 when the diag is set and is OOM: that diag stays. */
static int diag_oom(const Diag *diag) {
  return diag->set && diag->code != NULL && strcmp(diag->code, "OOM") == 0;
}

/* 1 when the matrix row of the footprint families F and G is IND_IF
   (quotient-lang S6 u4c2, USER rulings Q-S6-22 (a) and Q-S6-25 (b)). At
   that row the slot and the leaf check with the h forms of front.c. */
static int commute_if_row(const Checker *c, const char *f, const char *g) {
  int swap = 0;
  const IndRow *row = front_ind_row(&c->m->ind, f, g, &swap);
  return row != NULL && row->verdict == IND_IF;
}

/* A copy of D in the arena, or NULL when it is out of memory. */
static Decl *decl_copy(Checker *c, const Decl *d) {
  Decl *e = arena_alloc(c->m->arena, sizeof *e);
  if (e != NULL)
    *e = *d;
  return e;
}

/* A leaf com#leafN of the def commute at its pair (F, G) (quotient-lang
   S6 u4a, USER ruling Q-S6-12 (b)). A leaf that does not check gives
   REFUSE_COMMUTE at the pair and names the slot def commute<F><G>. */
static int check_commute_leaf(Checker *c, const Decl *d) {
  const char *f = pi_dom(d->type, 0u);
  const char *g = pi_dom(d->type, 1u);
  const Decl *use = d;
  if (commute_if_row(c, f, g)) {
    Decl *e = decl_copy(c, d);
    if (e == NULL)
      return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
    e->body = front_leaf_h_body(c->m->arena, d->body);
    if (e->body == NULL)
      return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
    use = e;
  }
  if (check_decl(c, use) || diag_oom(c->m->diag))
    return !c->m->diag->set;
  c->m->diag->set = 0;
  return diag_fail(c->m->diag, "REFUSE_COMMUTE", "commute", "the steps of %s and %s do not commute: at f : %s and g : %s, ind (body%s f) (body%s g) is not flagNo and effSeq (step (body%s f)) (step (body%s g)) does not convert to effSeq (step (body%s g)) (step (body%s f)); write the slot def commute%s%s : (f : %s) -> (g : %s) -> (s : State) -> Path (Maybe State) (effSeq (step (body%s f)) (step (body%s g)) s) (effSeq (step (body%s g)) (step (body%s f)) s) (USER ruling Q-S6-12 (b))", f, g, f, g, f, g, f, g, g, f, f, g, f, g, f, g, g, f);
}

/* The slot check com#slotN := commute<F><G> (USER ruling Q-S6-12 (b)): a
   slot with another type gives TYPE_MISMATCH at the slot. */
static int check_commute_slot(Checker *c, const Decl *d) {
  const char *f = pi_dom(d->type, 0u);
  const char *g = pi_dom(d->type, 1u);
  const char *slot = d->body != NULL && d->body->kind == TERM_VAR ? d->body->name : "?";
  int h = commute_if_row(c, f, g);
  const Decl *use = d;
  if (h) {
    Decl *e = decl_copy(c, d);
    if (e == NULL)
      return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
    e->type = front_slot_h_type(c->m->arena, d->type);
    if (e->type == NULL)
      return diag_fail(c->m->diag, "OOM", NULL, "out of memory");
    use = e;
  }
  if (check_decl(c, use) || diag_oom(c->m->diag))
    return !c->m->diag->set;
  c->m->diag->set = 0;
  if (h)
    return diag_fail(c->m->diag, "TYPE_MISMATCH", slot, "the slot %s must have the type (f : %s) -> (g : %s) -> (h : Path Flag (ind (body%s f) (body%s g)) flagYes) -> (s : State) -> Path (Maybe State) (effSeq (step (body%s f)) (step (body%s g)) s) (effSeq (step (body%s g)) (step (body%s f)) s) (USER ruling Q-S6-12 (b))", slot, f, g, f, g, f, g, g, f);
  return diag_fail(c->m->diag, "TYPE_MISMATCH", slot, "the slot %s must have the type (f : %s) -> (g : %s) -> (s : State) -> Path (Maybe State) (effSeq (step (body%s f)) (step (body%s g)) s) (effSeq (step (body%s g)) (step (body%s f)) s) (USER ruling Q-S6-12 (b))", slot, f, g, f, g, g, f);
}

/* The check of one decl: the ind placeholder, a commute leaf or slot
   check, or a normal decl. */
static int check_site(Checker *c, const Decl *d) {
  if (ind_site(d))
    return check_ind(c, d);
  if (commute_site(d, "com#leaf"))
    return check_commute_leaf(c, d);
  if (commute_site(d, "com#slot"))
    return check_commute_slot(c, d);
  return check_decl(c, d);
}

int check_program(Arena *arena, const DeclList *decls, Machine *m, Diag *diag, CheckMode mode) {
  Checker c;
  size_t ctors = 0;
  size_t extra = 0;
  size_t i;
  memset(m, 0, sizeof *m);
  m->arena = arena;
  m->diag = diag;
  m->fuel = EVAL_FUEL_STEPS;
  /* A cofamily with F fields elaborates to at most 2F + 4 definitions, one
     family and F + 1 constructors (S4). */
  for (i = 0; i < decls->count; i++) {
    size_t fields = decls->items[i].kind == DECL_COFAMILY && decls->items[i].ctor_count == 1u ? decls->items[i].ctors[0].field_count : 0u;
    int cofamily = decls->items[i].kind == DECL_COFAMILY;
    ctors += decls->items[i].ctor_count + (cofamily ? fields + 1u : 0u);
    extra += cofamily ? 2u * fields + 8u : 0u;
  }
  m->defs = arena_alloc(arena, (decls->count + extra + 1u) * sizeof *m->defs);
  m->families = arena_alloc(arena, (decls->count + extra + 1u) * sizeof *m->families);
  m->ctors = arena_alloc(arena, (ctors + 1u) * sizeof *m->ctors);
  m->spaces = arena_alloc(arena, (decls->count + 1u) * sizeof *m->spaces);
  if (m->defs == NULL || m->families == NULL || m->ctors == NULL || m->spaces == NULL)
    return diag_fail(diag, "OOM", NULL, "out of memory");
  m->def_cap = (uint32_t)(decls->count + extra);
  m->family_cap = (uint32_t)(decls->count + extra);
  m->ctor_cap = (uint32_t)ctors;
  m->space_cap = (uint32_t)decls->count;
  memset(&c, 0, sizeof c);
  c.m = m;
  c.decls = decls;
  c.mode = mode;
  for (i = 0; i < decls->count; i++) {
    checker_reset(&c, i, decls->items[i].name);
    if (!check_site(&c, &decls->items[i]))
      return 0;
    /* The other sorts of a block are checked with its first sort (S6). */
    i += decls->items[i].kind == DECL_FAMILY && decls->items[i].block_count > 1u ? decls->items[i].block_count - 1u : 0u;
  }
  /* The Ind matrix of the footprint families (S5 unit 5), when the def
     ind did not make it (Q-S6-11 (a)). */
  if (!m->ind.built && !ind_matrix(&c))
    return 0;
  m->def = NULL;
  return 1;
}

int entry_of(Machine *m, const Value *type, Entry *out) {
  const Value *t = type;
  memset(out, 0, sizeof *out);
  while (t != NULL && t->kind == VAL_PI && out->param_count < ENTRY_PARAMS_MAX) {
    if (!val_is(t->dom, OP_NAT) && !val_is(t->dom, OP_AMOUNT) && !val_is(t->dom, OP_FLAG))
      return 0;
    out->param_flag[out->param_count] = val_is(t->dom, OP_FLAG);
    t = closure_apply(m, t, val_var(m, out->param_count));
    out->param_count++;
  }
  /* An Option result prints its payload or none (S3). */
  out->result_option = val_is(t, OP_OPTION);
  t = out->result_option ? t->args[0] : t;
  out->result_flag = val_is(t, OP_FLAG);
  return val_is(t, OP_NAT) || val_is(t, OP_AMOUNT) || val_is(t, OP_FLAG);
}

static int parse_u64(const char *s, uint64_t *out) {
  uint64_t n = 0;
  size_t i;
  if (s[0] == '\0')
    return 0;
  for (i = 0; s[i] != '\0'; i++) {
    unsigned d = (unsigned)(unsigned char)s[i] - (unsigned)'0';
    if (d > 9u || n > (UINT64_MAX - d) / 10u)
      return 0;
    n = n * 10u + d;
  }
  *out = n;
  return 1;
}

/* The type of an entry argument. */
typedef enum { ARG_TYPE_NAT, ARG_TYPE_FLAG } ArgType;

static const char *const ARG_TEXT[] = {
  "Nat (0 to 2^64-1)", "Flag (0 or 1)",
};

/* An entry argument: a Nat in decimal or a Flag as 0 or 1. */
static const Value *entry_arg(Machine *m, const char *text, ArgType type) {
  uint64_t n = 0;
  const Value *v = NULL;
  switch (type) {
  case ARG_TYPE_NAT:
    v = parse_u64(text, &n) ? val_nat(m, n) : NULL;
    break;
  case ARG_TYPE_FLAG:
    v = parse_u64(text, &n) && n <= 1u ? val_make(m, n == 1u ? OP_FLAG_YES : OP_FLAG_NO, 0, 0, NULL, NULL, NULL) : NULL;
    break;
  }
  if (v == NULL && m->diag->code == NULL)
    diag_fail(m->diag, "EVAL_ARGS", m->def, "'%s' is not a %s", text, ARG_TEXT[type]);
  return v;
}

static int print_result(Machine *m, const char *name, const Value *v, FILE *out, FILE *err) {
  switch (v->kind) {
  case VAL_NAT:
    fprintf(out, "%llu\n", (unsigned long long)v->nat);
    return 0;
  case VAL_OP:
    if (val_is(v, OP_FLAG_YES) || val_is(v, OP_FLAG_NO)) {
      fprintf(out, "%d\n", val_is(v, OP_FLAG_YES));
      return 0;
    }
    if (val_is(v, OP_NONE)) {
      fputs("none\n", out);
      return 0;
    }
    if (val_is(v, OP_SOME))
      return print_result(m, name, v->args[0], out, err);
    break;
  case VAL_UNIV:
  case VAL_LAM:
  case VAL_PI:
  case VAL_SIGMA:
  case VAL_VAR:
  case VAL_APP:
  case VAL_STUCK:
  case VAL_PLAM:
  case VAL_PATHP:
  case VAL_IVAL:
  case VAL_PAPP:
    break;
  }
  diag_fail(m->diag, "EVAL_ENTRY", name, "the entry did not compute a number");
  return 1;
}

int eval_command(Machine *m, const char *name, char *const *args, int arg_count, FILE *out, FILE *err) {
  uint32_t d = find_def(m, name);
  Entry entry;
  const Value *v;
  char *buf;
  uint32_t i;
  m->def = name;
  if (d == NO_DEF) {
    diag_fail(m->diag, "EVAL_ENTRY", name, "no definition has this name");
    return 1;
  }
  v = def_value(m, d);
  if (v == NULL)
    return 1;
  if (!entry_of(m, m->defs[d].type, &entry) && arg_count != 0) {
    diag_fail(m->diag, "EVAL_ARGS", name, "the definition is not an entry, so it takes no arguments");
    return 2;
  }
  if (!entry_of(m, m->defs[d].type, &entry)) {
    buf = arena_alloc(m->arena, PRINT_MAX);
    if (buf == NULL)
      return diag_fail(m->diag, "OOM", name, "out of memory") + 1;
    if (!value_print(m, NULL, 0, v, buf, PRINT_MAX)) {
      diag_fail(m->diag, "EVAL_PRINT", name, "the normal form cannot be printed as source syntax");
      return 1;
    }
    fprintf(out, "%s\n", buf);
    return 0;
  }
  if ((uint32_t)arg_count != entry.param_count) {
    diag_fail(m->diag, "EVAL_ARGS", name, "the entry takes %u arguments, found %d", entry.param_count, arg_count);
    return 2;
  }
  for (i = 0; i < entry.param_count && v != NULL; i++) {
    const Value *arg = entry_arg(m, args[i], entry.param_flag[i] ? ARG_TYPE_FLAG : ARG_TYPE_NAT);
    v = arg == NULL ? NULL : apply_value(m, v, arg);
  }
  if (v == NULL)
    return strcmp(m->diag->code != NULL ? m->diag->code : "", "EVAL_ARGS") == 0 ? 2 : 1;
  return print_result(m, name, v, out, err);
}

static uint32_t find_family(const Machine *m, const char *name) {
  uint32_t i;
  for (i = 0; i < m->family_count; i++) {
    if (strcmp(m->families[i].name, name) == 0)
      return i;
  }
  return NO_FAMILY;
}

static int is_family(const Value *t, uint32_t family) {
  return t != NULL && val_is(t, OP_FAMILY) && t->inst == family;
}
