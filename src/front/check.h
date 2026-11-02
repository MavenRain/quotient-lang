/* The type checker, the refusals R1-R4 and the eval command. SHARED by the
   tcc kits. */
#ifndef LANG_FRONT_CHECK_H
#define LANG_FRONT_CHECK_H

#include "front/core.h"

#define ENTRY_PARAMS_MAX 32u /* 16 before sealed-lang S2 (R23): slashUsr takes 19 words */

/* An entry: a program definition of type Nat, Flag, or a function of Nat and
   Flag arguments to a Nat or Flag result. */
typedef struct {
  uint32_t param_count;
  int param_flag[ENTRY_PARAMS_MAX];
  int result_flag;
  int result_option;
} Entry;

/* Checks the domain declarations, then the program, into M. Returns 1, or 0
   after a diagnostic. */
/* The check mode (orbit-lang S3). In guest mode a program declaration
   cannot use a kit item (REFUSE_KIT). Kit mode is the trusted test scope of
   the kit gate (`langc --kit`). */
typedef enum {
  CHECK_GUEST,
  CHECK_KIT
} CheckMode;

int check_program(Arena *arena, const DeclList *decls, Machine *m, Diag *diag, CheckMode mode);
/* Returns 1 when TYPE is the type of an entry. */
int entry_of(Machine *m, const Value *type, Entry *out);
/* Evaluates the definition NAME on ARGS and prints the result. Returns 0, 1
   after a diagnostic, or 2 after an EVAL_ARGS diagnostic. */
int eval_command(Machine *m, const char *name, char *const *args, int arg_count, FILE *out, FILE *err);

#endif
