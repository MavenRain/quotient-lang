/* The first-order IR between the front end and a target. SHARED by the tcc
   kits.

   Each value is one unsigned 64-bit word: a Nat, a Flag (0 or 1), a
   constructor tag, or a heap address. Locals are numbered from 0. The
   parameters of an entry are locals 0 to param_count - 1. A heap block is a
   run of words. A target sets its own word width in memory (Wasm: 8 bytes,
   EVM: 32 bytes) and resets its bump allocator at each call. An entry has a
   static heap bound (heap_words); the lowering refuses an entry without one.

   Each op is total (S3): no expression traps, and a value has no trap
   flag. ADD and MUL wrap; ADD_CARRY gives 1 on an overflow. A heap block is
   word 0 = the tag, then field K at word 1 + K. */
#ifndef LANG_IR_H
#define LANG_IR_H

#include <stddef.h>
#include <stdint.h>

typedef enum {
  IR_SCALAR_NAT,
  IR_SCALAR_FLAG
} IrScalar;

typedef enum {
  IR_OP_ADD,       /* the sum modulo 2^64 */
  IR_OP_SUB,       /* truncates at 0 */
  IR_OP_MUL,       /* the product modulo 2^64 */
  IR_OP_EQ,        /* 1 when equal, else 0 */
  IR_OP_LE,        /* 1 when left <= right, else 0 */
  IR_OP_ADD_CARRY, /* 1 when the sum is larger than 2^64 - 1, else 0 */
  IR_OP_DIV,       /* the quotient; the right operand is a NonZero (S3) */
  IR_OP_MOD        /* the remainder; the right operand is a NonZero (S3) */
} IrOp;

typedef enum {
  IR_EXPR_CONST,  /* value */
  IR_EXPR_LOCAL,  /* local */
  IR_EXPR_BINARY, /* op left right */
  IR_EXPR_LOAD    /* word number field of the block at address left */
} IrExprKind;

typedef struct IrExpr IrExpr;
struct IrExpr {
  IrExprKind kind;
  uint64_t value;
  uint32_t local;
  IrOp op;
  uint32_t field;
  const IrExpr *left;
  const IrExpr *right;
};

typedef struct IrStmt IrStmt;

typedef struct {
  const IrStmt *const *items;
  size_t count;
} IrBlock;

typedef enum {
  IR_STMT_SET,    /* local := expr */
  IR_STMT_ALLOC,  /* local := address of a new block; word k := fields[k] */
  IR_STMT_IF,     /* expr != 0: body, else: otherwise */
  IR_STMT_SWITCH, /* run arms[expr]; a value outside 0 to arm_count - 1 runs the last arm */
  IR_STMT_REPEAT, /* counter := expr, then run body counter times */
  IR_STMT_WHILE,  /* counter := expr; run body while counter > 0 and local != 0,
                     counter decreasing by 1 at each run; body sets local */
  IR_STMT_RETURN  /* return expr */
} IrStmtKind;

struct IrStmt {
  IrStmtKind kind;
  uint32_t local;
  uint32_t counter;
  const IrExpr *expr;
  const IrExpr *const *fields;
  size_t field_count;
  IrBlock body;
  IrBlock otherwise;
  const IrBlock *arms;
  size_t arm_count;
};

/* The largest heap bound: 1 GiB of 8-byte words, the arena limit of langc
   eval. */
#define IR_HEAP_WORDS_MAX ((uint64_t)1 << 27)

/* One exported entry. The body block ends in RETURN on each path. */
typedef struct {
  const char *name;
  const IrScalar *params;
  size_t param_count;
  IrScalar result;
  uint32_t local_count; /* includes the parameters */
  IrBlock body;
  uint64_t heap_words; /* the ALLOC words on the longest path (S3) */
} IrFunc;

typedef struct {
  const IrFunc *funcs;
  size_t func_count;
} IrProgram;

#endif
