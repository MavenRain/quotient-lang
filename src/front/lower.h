/* The lowering from checked values to the IR, and the `langc ir` dump.
   SHARED by the tcc kits. */
#ifndef LANG_FRONT_LOWER_H
#define LANG_FRONT_LOWER_H

#include "front/core.h"
#include "ir.h"

/* Lowers each entry of the checked program M (a PROGRAM definition where
   entry_of holds) into PROG. Returns 1, or 0 after a diagnostic. */
int lower_program(Machine *m, IrProgram *prog);

/* The section quotient.footprint of a program with 1 or more footprint
   families (S9 u4, Q-S9-25 (a), Q-S9-27 (a)): IrProgram custom_name,
   custom_bytes and custom_size. A program with no footprint family keeps
   custom_name NULL. Returns 0 and a diagnostic when out of memory. */
int lower_footprint(Machine *m, const DeclList *decls, IrProgram *prog);

/* 1 when clause C of ROW is equal to an earlier clause of ROW (the print of
   the Ind matrix and the footprint section give each clause once). */
int ind_clause_seen(const IndRow *row, uint32_t c);
/* Writes PROG as text: a `func` line for each entry, then one statement on
   each line. */
void ir_print(const IrProgram *prog, FILE *out);

#endif
