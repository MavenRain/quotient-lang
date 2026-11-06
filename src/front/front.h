/* The front end entry point. SHARED by the tcc kits. */
#ifndef LANG_FRONT_FRONT_H
#define LANG_FRONT_FRONT_H

#include "front/core.h"
#include "front/parser.h"

#define SOURCE_MAX_BYTES ((size_t)1 << 20)

/* build/domain.c holds the bytes of domain/domain.lang (gen/embed.c). */
extern const unsigned char domain_source[];
extern const size_t domain_source_len;

/* Parses the embedded domain file, then the program, into one list. */
int front_load(Arena *arena, const char *source, const char *text, size_t len, DeclList *out, Diag *diag);

/* As front_load, with the extra domain text DOMAIN between the domain file
   and the program. The C regressions use it to declare a family. */
int front_load_domain(Arena *arena, const char *source, const char *domain, const char *text, size_t len, DeclList *out, Diag *diag);

/* The body of the def ind from the Ind matrix IND (quotient-lang S6, USER
   ruling Q-S6-11 (a)): `fun (a b : Body) => elim .. a`, each case an elim
   on b that gives flagYes for an IND_ALWAYS row and flagNo for the others.
   At an IND_IF row (F, G) with the slot def commute<F><G>, the case is the
   AND of the key tests of the row clauses (u4c2, USER ruling Q-S6-20 (a)).
   NULL when an allocation fails. */
const Term *front_ind_body(Arena *arena, const DeclList *decls, const IndMatrix *ind, int line, int col);

/* The matrix row of the footprint families A and B (either order), or
   NULL. *SWAP is 1 when the row is stored as (B, A) and A and B differ. */
const IndRow *front_ind_row(const IndMatrix *ind, const char *a, const char *b, int *swap);

/* The h forms at an IND_IF row (quotient-lang S6 u4c2, USER rulings
   Q-S6-22 (a) and Q-S6-25 (b)). front_slot_h_type gives the slot type
   `(f : F) -> (g : G) -> R` with the binder `(com#h : Path Flag (ind
   (bodyF f) (bodyG g)) flagYes)` in front of R. front_leaf_h_body gives
   the leaf body `fun f g h => funExt (S f g)` with `S f g` applied to h.
   A term of another form stays the same. NULL when an allocation fails. */
const Term *front_slot_h_type(Arena *arena, const Term *type);
const Term *front_leaf_h_body(Arena *arena, const Term *body);

#endif
