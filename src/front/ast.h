/* The syntax tree. SHARED by the tcc kits. Terms and types share one syntax. */
#ifndef LANG_FRONT_AST_H
#define LANG_FRONT_AST_H

#include <stddef.h>
#include <stdint.h>


typedef enum {
  TERM_VAR,   /* name */
  TERM_NAT,   /* nat */
  TERM_APP,   /* left applied to right */
  TERM_LAM,   /* fun (name : left) => right; left is NULL for a bare binder */
  TERM_PI,    /* (name : left) -> right; name is NULL for left -> right */
  TERM_SIGMA, /* Sigma (name : left) right, or (name : left) * right */
  TERM_UNIV,  /* Type nat */
  TERM_PAPP,  /* left @ right: a path applied to an interval term */
  TERM_INEG,  /* ~left */
  TERM_IMEET, /* left /\ right */
  TERM_IJOIN, /* left \/ right */
  /* [ k1 -> t1, ... ]: a list of TERM_SYSTEM cells. Left is a TERM_BRANCH
     (NULL in the cell of `[ ]`), right the next cell or NULL. Only the
     body of a `fun` can be a system (the tube of hcomp, S2 R2 (a)). */
  TERM_SYSTEM,
  TERM_BRANCH, /* left -> right: left the key, right the branch */
  TERM_APPEND  /* left ++ right: check.c selects the append def by the type of left (S6 u7, Q-S6-36 (a)) */
} TermKind;

typedef struct Term Term;
struct Term {
  TermKind kind;
  int line;
  int col;
  const char *name;
  uint64_t nat;
  const Term *left;
  const Term *right;
};

/* A named field of a constructor, or a parameter of a family. */
typedef struct {
  const char *name;
  const Term *type;
  int line;
  int col;
  int history; /* after the history marker of the state form (slice K3a) */
} Field;

typedef struct {
  const char *name;
  const Field *fields;
  size_t field_count;
  /* The result `: F params indices` after the fields of a constructor of an
     indexed family (S6), or NULL. */
  const Term *result;
  /* The boundary `[ k1 -> t1, ... ]` of a path constructor (a TERM_SYSTEM
     list), or NULL. */
  const Term *boundary;
  int line;
  int col;
} Ctor;

typedef enum {
  DECL_DEF,    /* def [rec] name : type := body */
  DECL_AXIOM,  /* axiom name : type */
  DECL_FAMILY, /* family name params [: index] := ctor | ... [and ...] */
  DECL_COFAMILY, /* cofamily name params := corec field* (S4): elaborated */
  DECL_KEYSPACE, /* keyspace Space : T (S5, X17): a key constructor T -> Key */
  DECL_STEP      /* step Fam b := [item, ...] (S5, Q-S5-10 (a)): the step items */
} DeclKind;

/* A family is legal only in the domain file (rule R1). ORIGIN_KIT is the
   kit prelude (orbit-lang S3, empty after S2): trusted as domain text, and its names
   are kit items outside the base span. */
typedef enum {
  ORIGIN_DOMAIN,
  ORIGIN_KIT,
  ORIGIN_PROGRAM
} Origin;

/* A key pattern argument (S5, X17): `b.field`, a Nat literal or the
   name of a closed def. */
typedef enum {
  PAT_ARG_FIELD,
  PAT_ARG_NAT,
  PAT_ARG_NAME
} PatArgKind;

typedef struct {
  PatArgKind kind;
  int line;
  int col;
  const char *base; /* PAT_ARG_FIELD: the name before '.' (the binder) */
  const char *name; /* PAT_ARG_FIELD: the field; PAT_ARG_NAME: the def */
  uint64_t nat;     /* PAT_ARG_NAT */
} PatArg;

/* A static key pattern `Space(arg, ...)` (S5, X17). */
typedef struct {
  int line;
  int col;
  const char *space;
  const PatArg *args;
  size_t arg_count;
} KeyPat;

/* The footprint clause of a family (S5, Q-S5-1 (a)):
   `footprint b reads [pat, ...] writes [pat, ...]`. */
typedef struct {
  int line;
  int col;
  const char *binder;
  const KeyPat *reads;
  size_t read_count;
  const KeyPat *writes;
  size_t write_count;
} FootprintDecl;

/* A step item (S5, X17, PLAN 5.2). `get x := pat` binds x : Val (Q-S5-3 (a)).
   `let x := term` has one form; a let at `Maybe T` aborts (Q-S5-4 (a)).
   `set pat := term` writes the key. */
typedef enum {
  STEP_GET,
  STEP_LET,
  STEP_SET
} StepItemKind;

typedef struct {
  StepItemKind kind;
  int line;
  int col;
  const char *name; /* STEP_GET and STEP_LET: the bound name */
  KeyPat pat;       /* STEP_GET and STEP_SET: the key pattern */
  const Term *term; /* STEP_LET and STEP_SET: the value */
} StepItem;

/* The step of a footprint family (S5, Q-S5-10 (a)):
   `step Fam b := [item, ...]`. The checker renames the binder b to the
   footprint binder before it compares a pattern (PLAN 5.2). */
typedef struct {
  int line;
  int col;
  const char *binder;
  const StepItem *items;
  size_t item_count;
} StepDecl;

typedef struct {
  DeclKind kind;
  Origin origin;
  int is_rec;
  int is_state; /* the state form, a family with the keyword state (slice K3a) */
  int is_sealed; /* `sealed family` (S5): guest elim and fold are law-only */
  int is_law;    /* `law def` (S5): the def is law-only (rule O7) */
  int line;
  int col;
  const char *name;
  const Term *type;
  const Term *body;
  const Field *params;
  size_t param_count;
  const Ctor *ctors;
  size_t ctor_count;
  /* The index telescope `: T1 -> ... -> Type 0` of a family (S6), or NULL
     for a uniform family. */
  const Term *index;
  /* The block of the declaration (S6): the list position of its first sort
     and the number of sorts. A declaration outside a block is a block of
     one. */
  size_t block_first;
  size_t block_count;
  /* The footprint clause of a family (S5, X17), or NULL. */
  const FootprintDecl *footprint;
  /* The step items of a `step` declaration (S5, Q-S5-10 (a)), or NULL. */
  const StepDecl *step;
} Decl;

/* Domain declarations come first, then the program. */
typedef struct {
  Decl *items;
  size_t count;
  size_t cap;
} DeclList;

#endif
