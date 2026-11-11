/* The langc command line. SHARED by the tcc kits.
   Exit 0: ok. Exit 1: the program is refused. Exit 2: usage or IO. */
#include <signal.h>
#include <stdio.h>
#include <string.h>

#include "front/check.h"
#include "front/front.h"
#include "front/lower.h"
#include "target.h"

#define ARENA_LIMIT_BYTES ((size_t)1 << 30)

typedef enum {
  CMD_CHECK,
  CMD_EVAL,
  CMD_IR,
  CMD_ABI,
  CMD_BUILD,
  CMD_IND,
} Command;

typedef struct {
  Command command;
  const char *prog_path;
  const char *entry;
  char **args;
  int arg_count;
  const char *out_path;
  int runtime;
  int json;
  CheckMode mode; /* orbit-lang S3: --kit selects the kit mode */
} Options;

static const struct {
  const char *word;
  Command command;
} COMMANDS[] = {
  {"check", CMD_CHECK},
  {"eval", CMD_EVAL},
  {"ir", CMD_IR},
  {"abi", CMD_ABI},
  {"build", CMD_BUILD},
  {"ind", CMD_IND},
};

static int usage(FILE *err) {
  fputs("usage: langc [--kit] check PROG [--json]\n"
        "       langc [--kit] eval PROG NAME [ARGS...]\n"
        "       langc [--kit] ir PROG\n"
        "       langc [--kit] abi PROG [--text]\n"
        "       langc [--kit] build PROG -o OUT [--runtime]\n"
        "       langc [--kit] ind PROG\n"
        "--kit: the kit mode, the trusted test scope of the kit gate\n", err);
  return 2;
}

static int find_command(const char *word, Command *out) {
  for (size_t i = 0; i < sizeof COMMANDS / sizeof COMMANDS[0]; i++) {
    if (strcmp(COMMANDS[i].word, word) == 0) {
      *out = COMMANDS[i].command;
      return 1;
    }
  }
  return 0;
}

static int parse_build_options(int argc, char **argv, Options *opt, Diag *diag) {
  for (int i = 3; i < argc; i++) {
    int is_out = strcmp(argv[i], "-o") == 0 && i + 1 < argc;
    int is_runtime = strcmp(argv[i], "--runtime") == 0;
    if (!is_out && !is_runtime) return diag_fail(diag, "USAGE", NULL, "unknown build argument '%s'", argv[i]);
    opt->out_path = is_out ? argv[i + 1] : opt->out_path;
    opt->runtime |= is_runtime;
    i += is_out;
  }
  return opt->out_path != NULL ? 1 : diag_fail(diag, "USAGE", NULL, "build needs -o OUT");
}

static int parse_options(int argc, char **argv, Options *opt, Diag *diag) {
  memset(opt, 0, sizeof *opt);
  if (argc < 3 || !find_command(argv[1], &opt->command)) {
    return diag_fail(diag, "USAGE", NULL, "expected a command and a program path");
  }
  opt->prog_path = argv[2];
  switch (opt->command) {
    case CMD_CHECK:
      /* u6b5: check --json also gives the O3 rows that the program uses. */
      opt->json = argc == 4 && strcmp(argv[3], "--json") == 0;
      return argc == 3 || opt->json ? 1 : diag_fail(diag, "USAGE", NULL, "check takes only --json after the program");
    case CMD_IND:
    case CMD_IR:
      return argc == 3 ? 1 : diag_fail(diag, "USAGE", NULL, "too many arguments");
    case CMD_ABI:
      /* The JSON ABI is the default; --text gives the C-K4-16 lines (C-c7-1). */
      opt->json = argc == 3;
      return argc == 3 || (argc == 4 && strcmp(argv[3], "--text") == 0) ? 1
        : diag_fail(diag, "USAGE", NULL, "abi takes only --text after the program");
    case CMD_EVAL:
      if (argc < 4) return diag_fail(diag, "USAGE", NULL, "eval needs a definition name");
      opt->entry = argv[3];
      opt->args = argv + 4;
      opt->arg_count = argc - 4;
      return 1;
    case CMD_BUILD:
      return parse_build_options(argc, argv, opt, diag);
  }
  return 0;
}

static int read_source(Arena *arena, const char *path, char **out, size_t *len, Diag *diag) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) return diag_fail(diag, "IO", NULL, "cannot open %s", path);
  char *buf = arena_alloc(arena, SOURCE_MAX_BYTES + 1);
  size_t count = buf == NULL ? 0 : fread(buf, 1, SOURCE_MAX_BYTES + 1, file);
  int read_error = ferror(file);
  fclose(file);
  if (buf == NULL) return diag_fail(diag, "OOM", NULL, "no memory for %s", path);
  if (read_error) return diag_fail(diag, "IO", NULL, "cannot read %s", path);
  if (count > SOURCE_MAX_BYTES) return diag_fail(diag, "IO_SIZE", NULL, "%s is larger than %zu bytes", path, SOURCE_MAX_BYTES);
  *out = buf;
  *len = count;
  return 1;
}

/* Lowers the entries, then runs the ir, abi or build command. */
static int run_target(const Options *opt, Machine *machine, Diag *diag) {
  IrProgram prog;
  FILE *out;
  size_t i;
  int ok = 1;
  if (!lower_program(machine, &prog)) return 1;
  switch (opt->command) {
    case CMD_IR:
      ir_print(&prog, stdout);
      return 0;
    case CMD_ABI:
      for (i = 0; i < prog.func_count && ok; i++) ok = target_abi_line(&prog.funcs[i], stdout, stderr);
      return ok ? 0 : 1;
    case CMD_CHECK:
    case CMD_EVAL:
    case CMD_BUILD:
    case CMD_IND:
      break;
  }
  out = fopen(opt->out_path, "wb");
  if (out == NULL) return diag_fail(diag, "IO", NULL, "cannot write '%s'", opt->out_path) + 1;
  ok = target_write(&prog, opt->runtime ? TARGET_PART_RUNTIME : TARGET_PART_MAIN, out, stderr);
  return fclose(out) == 0 && ok ? 0 : 1;
}

/* Prints the Ind operand OPD: `a.NAME`, `b.NAME`, the closed def name or the
   numeral (S5 unit 5, Q-S5-32 (a)). */
static void ind_operand_print(const IndOperand *opd, FILE *out) {
  switch (opd->kind) {
    case IND_OPD_FIELD_A:
      fprintf(out, "a.%s", opd->name);
      return;
    case IND_OPD_FIELD_B:
      fprintf(out, "b.%s", opd->name);
      return;
    case IND_OPD_CONST:
      if (opd->name != NULL) {
        fputs(opd->name, out);
      } else {
        fprintf(out, "%llu", (unsigned long long)opd->nat);
      }
      return;
  }
}

/* Returns 1 when the Ind operands X and Y are the same operand. */
static int ind_operand_same(const IndOperand *x, const IndOperand *y) {
  if (x->kind != y->kind) return 0;
  if (x->name == NULL || y->name == NULL) return x->name == y->name && x->nat == y->nat;
  return strcmp(x->name, y->name) == 0;
}

/* Returns 1 when the clauses X and Y have the same literals in the same order. */
static int ind_clause_same(const IndClause *x, const IndClause *y) {
  if (x->lit_count != y->lit_count) return 0;
  for (uint32_t l = 0; l < x->lit_count; l++) {
    if (!ind_operand_same(&x->lits[l].left, &y->lits[l].left)) return 0;
    if (!ind_operand_same(&x->lits[l].right, &y->lits[l].right)) return 0;
  }
  return 1;
}

/* Returns 1 when clause C of ROW is equal to an earlier clause of ROW. */
static int ind_clause_seen(const IndRow *row, uint32_t c) {
  for (uint32_t e = 0; e < c; e++) {
    if (ind_clause_same(&row->clauses[e], &row->clauses[c])) return 1;
  }
  return 0;
}

/* Prints the Ind matrix IND (S5 unit 5, Q-S5-32 (a)): one line for each row in
   row order, `A B: ind`, `A B: dep` or `A B: ind-if C1 and C2`. A clause is
   `(L1 or L2)` and a literal is `X != Y`. A clause that is equal to an earlier
   clause of the row is not printed again (the AND is idempotent). Returns 0,
   or 1 on a write error. */
static int ind_print(const IndMatrix *ind, FILE *out) {
  for (uint32_t r = 0; r < ind->row_count; r++) {
    const IndRow *row = &ind->rows[r];
    uint32_t shown = 0;
    fprintf(out, "%s %s: ", row->a, row->b);
    switch (row->verdict) {
      case IND_ALWAYS:
        fputs("ind", out);
        break;
      case IND_DEP:
        fputs("dep", out);
        break;
      case IND_IF:
        fputs("ind-if", out);
        for (uint32_t c = 0; c < row->clause_count; c++) {
          if (ind_clause_seen(row, c)) continue;
          const IndClause *clause = &row->clauses[c];
          fputs(shown == 0 ? " (" : " and (", out);
          shown++;
          for (uint32_t l = 0; l < clause->lit_count; l++) {
            fputs(l == 0 ? "" : " or ", out);
            ind_operand_print(&clause->lits[l].left, out);
            fputs(" != ", out);
            ind_operand_print(&clause->lits[l].right, out);
          }
          fputs(")", out);
        }
        break;
    }
    fputs("\n", out);
  }
  return ferror(out) ? 1 : 0;
}

/* u6b5: mark each definition that t reaches through CORE_GLOBAL. The rows
   are the rows of history_ok (check.c). A NULL child is a leaf. */
static void core_reach(const Machine *m, const Core *t, unsigned char *seen) {
  uint32_t i;
  if (t == NULL)
    return;
  switch (t->kind) {
  case CORE_VAR:
  case CORE_NAT:
  case CORE_UNIV:
  case CORE_IZERO:
  case CORE_IONE:
    return;
  case CORE_GLOBAL:
    if (t->index < m->def_count && !seen[t->index]) {
      seen[t->index] = 1;
      core_reach(m, m->defs[t->index].body, seen);
    }
    return;
  case CORE_LAM:
  case CORE_PI:
  case CORE_SIGMA:
  case CORE_PLAM:
  case CORE_APP:
  case CORE_INEG:
  case CORE_IMEET:
  case CORE_IJOIN:
    core_reach(m, t->a, seen);
    core_reach(m, t->b, seen);
    return;
  case CORE_PATHP:
  case CORE_PAPP:
    core_reach(m, t->a, seen);
    core_reach(m, t->b, seen);
    core_reach(m, t->args[0], seen);
    core_reach(m, t->args[1], seen);
    return;
  case CORE_OP:
    /* Readback can embed an assumption in a refl body without a global. */
    if (t->op == OP_AXIOM && t->inst < m->def_count)
      seen[t->inst] = 1;
    for (i = 0; i < t->argc; i++)
      core_reach(m, t->args[i], seen);
    return;
  }
}

/* u6b5: check --json. The O3 rows (the defs with an OP_AXIOM body) that a
   program definition reaches, in definition order. */
static int axioms_print(const Machine *m, FILE *out) {
  unsigned char seen[m->def_count + 1u];
  uint32_t i;
  int first = 1;
  memset(seen, 0, sizeof seen);
  for (i = 0; i < m->def_count; i++) {
    if (m->defs[i].origin == ORIGIN_PROGRAM)
      core_reach(m, m->defs[i].body, seen);
  }
  fputs("{\"ok\":true,\"axioms\":[", out);
  for (i = 0; i < m->def_count; i++) {
    const Core *b = m->defs[i].body;
    if (seen[i] && b != NULL && b->kind == CORE_OP && b->op == OP_AXIOM) {
      fprintf(out, "%s\"%s\"", first ? "" : ",", m->defs[i].name);
      first = 0;
    }
  }
  fputs("]}\n", out);
  return ferror(out) ? 1 : 0;
}

static int run(const Options *opt, Arena *arena, Diag *diag) {
  char *text = NULL;
  size_t len = 0;
  if (!read_source(arena, opt->prog_path, &text, &len, diag)) return 2;
  DeclList decls;
  if (!front_load(arena, opt->prog_path, text, len, &decls, diag)) return 1;
  Machine machine;
  if (!check_program(arena, &decls, &machine, diag, opt->mode)) return 1;
  switch (opt->command) {
    case CMD_CHECK:
      if (opt->json) return axioms_print(&machine, stdout);
      puts("ok");
      return 0;
    case CMD_EVAL:
      return eval_command(&machine, opt->entry, opt->args, opt->arg_count, stdout, stderr);
    case CMD_IND:
      return ind_print(&machine.ind, stdout);
    case CMD_IR:
    case CMD_ABI:
    case CMD_BUILD:
      break;
  }
  return run_target(opt, &machine, diag);
}

int main(int argc, char **argv) {
  Diag diag;
  diag_init(&diag);
  Options opt;
  int kit = argc > 1 && strcmp(argv[1], "--kit") == 0;
  if (!parse_options(argc - kit, argv + kit, &opt, &diag)) {
    diag_print(&diag, stderr);
    return usage(stderr);
  }
  opt.mode = kit ? CHECK_KIT : CHECK_GUEST;
  Arena arena;
  arena_init(&arena, ARENA_LIMIT_BYTES);
  int status = run(&opt, &arena, &diag);
  arena_release(&arena);
  if (status != 0) diag_print(&diag, stderr);
  return status;
}
