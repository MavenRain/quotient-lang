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
  CMD_FOOTPRINT,
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
  {"footprint", CMD_FOOTPRINT},
};

static int usage(FILE *err) {
  fputs("usage: langc [--kit] check PROG [--json]\n"
        "       langc [--kit] eval PROG NAME [ARGS...]\n"
        "       langc [--kit] ir PROG\n"
        "       langc [--kit] abi PROG [--text]\n"
        "       langc [--kit] build PROG -o OUT [--runtime]\n"
        "       langc [--kit] ind PROG\n"
        "       langc footprint MODULE.wasm\n"
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
    case CMD_FOOTPRINT:
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

/* Lowers the entries and the footprint section (S9 u4), then runs the ir,
   abi or build command. */
static int run_target(const Options *opt, const DeclList *decls, Machine *machine, Diag *diag) {
  IrProgram prog;
  FILE *out;
  size_t i;
  int ok = 1;
  if (!lower_program(machine, &prog) || !lower_footprint(machine, decls, &prog)) return 1;
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
    case CMD_FOOTPRINT:
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

/* Q-S9-26 (a): `langc footprint MODULE.wasm` reads the bytes of a module
   (no source) and prints its `quotient.footprint` section (Q-S9-25 (a)):
   one line for each family, then the Ind rows in the form of `langc ind`.
   A module with no such section gives no output. Each read has a bounds
   check; a first pass checks the whole section before the print pass. */
typedef struct {
  const unsigned char *buf;
  size_t len;
  size_t pos;
  int ok;
} FpIn;

static unsigned fd_byte(FpIn *in) {
  unsigned v = in->ok && in->pos < in->len ? in->buf[in->pos] : 0u;
  in->ok = in->ok && in->pos < in->len;
  in->pos += in->ok ? 1u : 0u;
  return v;
}

static uint64_t fd_uleb(FpIn *in) {
  uint64_t v = 0;
  unsigned shift = 0;
  unsigned b = 0x80u;
  while (in->ok && (b & 0x80u) != 0) {
    b = fd_byte(in);
    in->ok = in->ok && shift < 64 && (shift != 63 || (b & 0xFEu) == 0);
    v |= shift < 64 ? (uint64_t)(b & 0x7Fu) << shift : 0;
    shift += 7;
  }
  return v;
}

/* A name: a uleb length, then the bytes; the copy ends with a NUL. */
static char *fd_name(FpIn *in, Arena *arena) {
  uint64_t n = fd_uleb(in);
  char *s = NULL;
  in->ok = in->ok && n <= in->len - in->pos;
  s = in->ok ? arena_alloc(arena, (size_t)n + 1) : NULL;
  in->ok = in->ok && s != NULL;
  if (!in->ok) return NULL;
  memcpy(s, in->buf + in->pos, (size_t)n);
  s[n] = '\0';
  in->pos += (size_t)n;
  return s;
}

static void fd_put(const FpIn *in, FILE *out, const char *s) {
  if (out != NULL && in->ok) fputs(s, out);
}

/* A pattern argument (Q-S9-31 (a)): 0 and a field name (printed
   BINDER.field), 1 and a numeral, or 2 and a def name. */
static void fd_pat_arg(FpIn *in, Arena *arena, const char *binder, FILE *out) {
  unsigned kind = fd_byte(in);
  char *name = kind == 1 ? NULL : fd_name(in, arena);
  uint64_t nat = kind == 1 ? fd_uleb(in) : 0;
  in->ok = in->ok && kind <= 2;
  if (out == NULL || !in->ok) return;
  if (kind == 0) fprintf(out, "%s.", binder);
  if (kind == 1) fprintf(out, "%llu", (unsigned long long)nat);
  else fputs(name, out);
}

/* A key pattern: the space name, arg_count, then each argument. */
static void fd_pattern(FpIn *in, Arena *arena, const char *binder, FILE *out) {
  char *space = fd_name(in, arena);
  uint64_t n = fd_uleb(in);
  uint64_t i;
  fd_put(in, out, space);
  fd_put(in, out, n == 0 ? "" : "(");
  for (i = 0; i < n && in->ok; i++) {
    fd_put(in, out, i == 0 ? "" : ", ");
    fd_pat_arg(in, arena, binder, out);
  }
  fd_put(in, out, n == 0 ? "" : ")");
}

/* A pattern list: the count, then each pattern. */
static void fd_list(FpIn *in, Arena *arena, const char *binder, const char *head, FILE *out) {
  uint64_t n = fd_uleb(in);
  uint64_t i;
  fd_put(in, out, head);
  for (i = 0; i < n && in->ok; i++) {
    fd_put(in, out, i == 0 ? "" : ", ");
    fd_pattern(in, arena, binder, out);
  }
  fd_put(in, out, "]");
}

/* A family record: its name, its binder name, the reads, the writes. */
static char *fd_family(FpIn *in, Arena *arena, FILE *out) {
  char *name = fd_name(in, arena);
  char *binder = fd_name(in, arena);
  if (out != NULL && in->ok) fprintf(out, "%s: footprint %s", name, binder);
  fd_list(in, arena, binder, " reads [", out);
  fd_list(in, arena, binder, " writes [", out);
  fd_put(in, out, "\n");
  return name;
}

/* An Ind operand (Q-S9-33 (a)): 0 a field of family a, 1 a Nat, 2 a closed
   def, 3 a field of family b. */
static void fd_operand(FpIn *in, Arena *arena, FILE *out) {
  IndOperand x;
  unsigned kind = fd_byte(in);
  memset(&x, 0, sizeof x);
  x.kind = kind == 0 ? IND_OPD_FIELD_A : kind == 3 ? IND_OPD_FIELD_B : IND_OPD_CONST;
  x.name = kind == 1 ? NULL : fd_name(in, arena);
  x.nat = kind == 1 ? fd_uleb(in) : 0;
  in->ok = in->ok && kind <= 3;
  if (out != NULL && in->ok) ind_operand_print(&x, out);
}

/* A row: the family indexes of a and b, the verdict byte (0 ind, 1 dep and
   the space name, 2 ind-if and the clauses, Q-S9-34 (a)). */
static void fd_row(FpIn *in, Arena *arena, char *const *names, uint64_t count, FILE *out) {
  uint64_t a = fd_uleb(in);
  uint64_t b = fd_uleb(in);
  unsigned verdict;
  uint64_t clauses;
  uint64_t c;
  in->ok = in->ok && a < count && b < count;
  verdict = fd_byte(in);
  in->ok = in->ok && verdict <= 2;
  if (out != NULL && in->ok) fprintf(out, "%s %s: %s", names[a], names[b], verdict == 0 ? "ind" : verdict == 1 ? "dep" : "ind-if");
  if (verdict == 1) (void)fd_name(in, arena);
  clauses = verdict == 2 ? fd_uleb(in) : 0;
  for (c = 0; c < clauses && in->ok; c++) {
    uint64_t lits = fd_uleb(in);
    uint64_t l;
    fd_put(in, out, c == 0 ? " (" : " and (");
    for (l = 0; l < lits && in->ok; l++) {
      fd_put(in, out, l == 0 ? "" : " or ");
      fd_operand(in, arena, out);
      fd_put(in, out, " != ");
      fd_operand(in, arena, out);
    }
    fd_put(in, out, ")");
  }
  fd_put(in, out, "\n");
}

/* The section payload: the version 1, family_count and each family, then
   row_count and each row; no byte after the last row. */
static int fd_section(FpIn *in, Arena *arena, FILE *out) {
  uint64_t count;
  uint64_t rows;
  uint64_t i;
  char **names;
  in->ok = in->ok && fd_byte(in) == 1;
  count = fd_uleb(in);
  in->ok = in->ok && count <= in->len - in->pos;
  names = in->ok ? arena_alloc(arena, (size_t)count * sizeof *names + 1) : NULL;
  in->ok = in->ok && names != NULL;
  for (i = 0; i < count && in->ok; i++)
    names[i] = fd_family(in, arena, out);
  rows = fd_uleb(in);
  for (i = 0; i < rows && in->ok; i++)
    fd_row(in, arena, names, count, out);
  return in->ok && in->pos == in->len;
}

/* The name of a custom section at start (size bytes): 1 when the name is
   `quotient.footprint` (*payload: the first byte after the name), 0 for an
   other name, -1 when the name does not fit in the section. */
static int fd_is_footprint(const unsigned char *buf, size_t start, size_t size, size_t *payload) {
  static const char want[] = "quotient.footprint";
  FpIn in = {buf, start + size, start, 1};
  uint64_t n = fd_uleb(&in);
  if (!in.ok || n > in.len - in.pos) return -1;
  *payload = in.pos + (size_t)n;
  return n == sizeof want - 1 && memcmp(buf + in.pos, want, sizeof want - 1) == 0;
}

/* The count of `quotient.footprint` sections in a module (*sec: the payload
   of the last one), or -1 when the bytes are not a module. */
static int fd_custom(const unsigned char *buf, size_t len, FpIn *sec) {
  static const unsigned char head[8] = {0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00};
  FpIn in = {buf, len, 8, 1};
  int found = 0;
  if (len < 8 || memcmp(buf, head, 8) != 0) return -1;
  while (in.ok && in.pos < len) {
    unsigned id = fd_byte(&in);
    uint64_t size = fd_uleb(&in);
    size_t start = in.pos;
    size_t payload = 0;
    int named;
    if (!in.ok || size > len - start) return -1;
    named = id == 0 ? fd_is_footprint(buf, start, (size_t)size, &payload) : 0;
    if (named < 0) return -1;
    found += named;
    if (named == 1) {
      sec->buf = buf;
      sec->len = start + (size_t)size;
      sec->pos = payload;
      sec->ok = 1;
    }
    in.pos = start + (size_t)size;
  }
  return found;
}

/* The bytes of a file, in the arena. */
static int read_bytes(Arena *arena, const char *path, unsigned char **buf, size_t *len, Diag *diag) {
  FILE *f = fopen(path, "rb");
  long size;
  if (f == NULL) return diag_fail(diag, "IO", NULL, "cannot read '%s'", path);
  size = fseek(f, 0, SEEK_END) == 0 ? ftell(f) : -1;
  *buf = size >= 0 && fseek(f, 0, SEEK_SET) == 0 ? arena_alloc(arena, (size_t)size + 1) : NULL;
  *len = *buf != NULL ? fread(*buf, 1, (size_t)size, f) : 0;
  fclose(f);
  return *buf != NULL && *len == (size_t)size ? 1 : diag_fail(diag, "IO", NULL, "cannot read '%s'", path);
}

static int footprint_command(const char *path, Arena *arena, Diag *diag) {
  unsigned char *buf = NULL;
  size_t len = 0;
  FpIn sec = {NULL, 0, 0, 0};
  FpIn pass;
  int found;
  if (!read_bytes(arena, path, &buf, &len, diag)) return 2;
  found = fd_custom(buf, len, &sec);
  if (found < 0) return diag_fail(diag, "FOOTPRINT", NULL, "'%s' is not a Wasm module", path) + 1;
  if (found > 1) return diag_fail(diag, "FOOTPRINT", NULL, "'%s' has more than one quotient.footprint section", path) + 1;
  pass = sec;
  if (found == 1 && !fd_section(&pass, arena, NULL))
    return diag_fail(diag, "FOOTPRINT", NULL, "the quotient.footprint section of '%s' is not valid", path) + 1;
  pass = sec;
  if (found == 1) (void)fd_section(&pass, arena, stdout);
  return ferror(stdout) ? 1 : 0;
}

static int run(const Options *opt, Arena *arena, Diag *diag) {
  if (opt->command == CMD_FOOTPRINT) return footprint_command(opt->prog_path, arena, diag);
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
    case CMD_FOOTPRINT:
      break;
  }
  return run_target(opt, &decls, &machine, diag);
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
