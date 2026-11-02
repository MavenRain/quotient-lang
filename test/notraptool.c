/* The no-trap check of a module of the writer (src/wasm.c), S3. Usage:
 * notraptool FILE.wasm.
 * When the module is good, the tool exits 0 and prints nothing. At the first
 * failure, it prints one line `notraptool: FILE: REASON` on stderr and exits
 * 1. A usage error, or a file that the tool cannot read, gives exit 2.
 *
 * The tool reads the header (the magic and version 1), then each section by
 * its id and size. Memory section: each memory must have a maximum, and the
 * maximum must be equal to the minimum. Code section: the tool skips the
 * locals of each body, then decodes each instruction with the list of
 * src/wasmop.h. A body must not have `unreachable`, `memory.grow`, a byte
 * that is not in the list, or an i64.div_u or i64.rem_u that does not come
 * after the guard of divisor() in src/wasm.c. Each read checks the size
 * first, so a short module fails with `truncated`. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "wasmop.h"

#define NOTRAP_ENUM(name, byte, imm) name = byte,
enum { WASM_OPS(NOTRAP_ENUM) };
#undef NOTRAP_ENUM

enum {
  MODULE_MAX = 1 << 20, /* the largest module: 1 MiB */
  GUARD_LEN = 5,        /* the instructions of the divisor guard */
  SECTION_MEMORY = 5,
  SECTION_CODE = 10
};

/* One row of the list: the opcode byte and the kind of its immediate. */
typedef struct {
  unsigned byte;
  int imm;
} Op;

#define NOTRAP_ROW(name, byte, imm) {byte, imm},
static const Op ops[] = {WASM_OPS(NOTRAP_ROW)};
#undef NOTRAP_ROW

/* A decoded instruction: the opcode and the first number of its immediate
 * (0 when it has no immediate). */
typedef struct {
  unsigned op;
  uint64_t imm;
} Insn;

/* The module bytes from POS to END, and the reason of the first failure. */
typedef struct {
  const unsigned char *bytes;
  size_t pos;
  size_t end;
  const char *why;
  char text[48];
} Reader;

static unsigned char module[MODULE_MAX + 1];

static int fail(Reader *r, const char *why) {
  if (r->why == NULL) r->why = why;
  return 0;
}

static int get_byte(Reader *r, unsigned *v) {
  if (r->pos >= r->end) return fail(r, "truncated");
  *v = r->bytes[r->pos++];
  return 1;
}

/* A LEB128 of BITS bits or less. For a signed LEB128, the tool keeps the
 * bits and does not extend the sign. */
static int get_leb(Reader *r, unsigned bits, uint64_t *v) {
  unsigned shift;
  unsigned b = 0x80u;
  int ok = 1;
  *v = 0;
  for (shift = 0; ok && (b & 0x80u) != 0; shift += 7) {
    ok = (shift < bits || fail(r, "LEB128 too long")) && get_byte(r, &b);
    *v |= ok ? (uint64_t)(b & 0x7Fu) << shift : 0;
  }
  return ok;
}

/* The row of the opcode BYTE in the list, or NULL. */
static const Op *find_op(unsigned byte) {
  size_t k;
  for (k = 0; k < sizeof ops / sizeof ops[0]; k++)
    if (ops[k].byte == byte) return &ops[k];
  return NULL;
}

/* Reads an immediate of the kind KIND. *FIRST gets its first number. */
static int immediate(Reader *r, int kind, uint64_t *first) {
  uint64_t n = 0;
  uint64_t k;
  uint64_t label;
  int ok;
  switch (kind) {
    case WASM_IMM_NONE:
      return 1;
    case WASM_IMM_BLOCKTYPE: /* a type byte, or a type index (33 bits) */
      return get_leb(r, 33, first);
    case WASM_IMM_LABEL:
    case WASM_IMM_INDEX:
      return get_leb(r, 32, first);
    case WASM_IMM_LABELS: /* N, then N labels and the default label */
      ok = get_leb(r, 32, &n);
      for (k = 0; k <= n && ok; k++) ok = get_leb(r, 32, &label);
      return ok;
    case WASM_IMM_MEMARG:
      return get_leb(r, 32, first) && get_leb(r, 32, &label);
    case WASM_IMM_I32:
      return get_leb(r, 32, first);
    case WASM_IMM_I64:
      return get_leb(r, 64, first);
  }
  return fail(r, "an immediate kind outside the list");
}

/* The guard of divisor() in src/wasm.c: local.get Y, local.get Y, i64.eqz,
 * i64.extend_i32_u, i64.or leave Y | (Y = 0), which is never 0. LAST holds
 * the GUARD_LEN instructions before the division, the oldest first. */
static int guarded(const Insn *last) {
  return last[0].op == OP_LOCAL_GET && last[1].op == OP_LOCAL_GET && last[1].imm == last[0].imm &&
         last[2].op == OP_I64_EQZ && last[3].op == OP_I64_EXTEND_I32_U && last[4].op == OP_I64_OR;
}

/* Decodes one instruction, then adds it to LAST. */
static int check_insn(Reader *r, Insn *last) {
  Insn cur = {0, 0};
  const Op *row;
  int ok = get_byte(r, &cur.op);
  if (!ok) return 0;
  if (cur.op == 0x00u) return fail(r, "unreachable");
  if (cur.op == 0x40u) return fail(r, "memory.grow");
  row = find_op(cur.op);
  if (row == NULL) {
    snprintf(r->text, sizeof r->text, "opcode 0x%02X outside the list", cur.op);
    return fail(r, r->text);
  }
  if ((cur.op == OP_I64_DIV_U || cur.op == OP_I64_REM_U) && !guarded(last))
    return fail(r, "div_u or rem_u with no guard");
  ok = immediate(r, row->imm, &cur.imm);
  memmove(last, last + 1, (GUARD_LEN - 1) * sizeof *last);
  last[GUARD_LEN - 1] = cur;
  return ok;
}

/* One function body: its size, the locals (a count, then each group: a
 * count and a type), then the instructions. */
static int check_body(Reader *r) {
  Insn last[GUARD_LEN] = {{0, 0}};
  size_t outer = r->end;
  uint64_t size = 0;
  uint64_t n = 0;
  uint64_t i;
  uint64_t count;
  unsigned type;
  int ok = get_leb(r, 32, &size) && (size <= r->end - r->pos || fail(r, "truncated"));
  if (!ok) return 0;
  r->end = r->pos + (size_t)size;
  ok = get_leb(r, 32, &n);
  for (i = 0; i < n && ok; i++) ok = get_leb(r, 32, &count) && get_byte(r, &type);
  while (ok && r->pos < r->end) ok = check_insn(r, last);
  r->end = outer;
  return ok;
}

static int check_code(Reader *r) {
  uint64_t n = 0;
  uint64_t i;
  int ok = get_leb(r, 32, &n);
  for (i = 0; i < n && ok; i++) ok = check_body(r);
  return ok;
}

/* One memory: the flags (1: a minimum and a maximum), then the limits. */
static int check_limits(Reader *r) {
  unsigned flags = 0;
  uint64_t min = 0;
  uint64_t max = 0;
  int ok = get_byte(r, &flags) && get_leb(r, 32, &min);
  if (!ok) return 0;
  if (flags == 0x00u) return fail(r, "memory with no max");
  if (flags != 0x01u) {
    snprintf(r->text, sizeof r->text, "memory flags 0x%02X", flags);
    return fail(r, r->text);
  }
  return get_leb(r, 32, &max) && (max == min || fail(r, "memory max is not equal to min"));
}

static int check_memory(Reader *r) {
  uint64_t n = 0;
  uint64_t i;
  int ok = get_leb(r, 32, &n);
  for (i = 0; i < n && ok; i++) ok = check_limits(r);
  return ok;
}

/* One section: its id, its size, then its contents. The tool checks the
 * memory section and the code section, and skips the other sections. */
static int check_section(Reader *r) {
  size_t outer = r->end;
  unsigned id = 0;
  uint64_t size = 0;
  int ok = get_byte(r, &id) && get_leb(r, 32, &size) && (size <= r->end - r->pos || fail(r, "truncated"));
  if (!ok) return 0;
  r->end = r->pos + (size_t)size;
  switch (id) {
    case SECTION_MEMORY:
      ok = check_memory(r);
      break;
    case SECTION_CODE:
      ok = check_code(r);
      break;
    default:
      r->pos = r->end;
      break;
  }
  ok = ok && (r->pos == r->end || fail(r, "a section size does not match its contents"));
  r->end = outer;
  return ok;
}

static int check_module(Reader *r) {
  static const unsigned char header[8] = {0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00};
  int ok = (r->end >= sizeof header || fail(r, "truncated")) &&
           (memcmp(r->bytes, header, sizeof header) == 0 || fail(r, "no wasm magic and version 1"));
  r->pos = ok ? sizeof header : 0;
  while (ok && r->pos < r->end) ok = check_section(r);
  return ok;
}

int main(int argc, char **argv) {
  Reader r = {module, 0, 0, NULL, {0}};
  FILE *f;
  int bad;
  int ok;
  if (argc != 2) {
    fputs("usage: notraptool FILE.wasm\n", stderr);
    return 2;
  }
  f = fopen(argv[1], "rb");
  if (f == NULL) {
    fprintf(stderr, "notraptool: %s: cannot open the file\n", argv[1]);
    return 2;
  }
  r.end = fread(module, 1, sizeof module, f);
  bad = ferror(f);
  fclose(f);
  if (bad) {
    fprintf(stderr, "notraptool: %s: cannot read the file\n", argv[1]);
    return 2;
  }
  ok = r.end <= MODULE_MAX ? check_module(&r) : fail(&r, "the module is larger than 1 MiB");
  if (ok) return 0;
  fprintf(stderr, "notraptool: %s: %s\n", argv[1], r.why == NULL ? "no reason" : r.why);
  return 1;
}
