/* The Wasm opcodes of the writer (src/wasm.c): one list for the writer, for
   test/notraptool.c and for the S8 engine (S3). An entry
   X(NAME, BYTE, IMM) gives the opcode name, its byte and the kind of its
   immediate. The list holds only the opcodes that the writer emits. It
   has no `unreachable` and no `memory.grow`: a module of
   the writer does not trap on them. */
#ifndef LANG_WASMOP_H
#define LANG_WASMOP_H

/* The kind of the immediate after an opcode (LEB128 is the integer encoding
   of the Wasm binary format). */
enum {
  WASM_IMM_NONE,      /* no immediate */
  WASM_IMM_BLOCKTYPE, /* one block type byte */
  WASM_IMM_LABEL,     /* one label index, an unsigned LEB128 */
  WASM_IMM_LABELS,    /* a count N, N label indexes, then the default label */
  WASM_IMM_INDEX,     /* one function, local or global index */
  WASM_IMM_MEMARG,    /* the alignment, then the offset */
  WASM_IMM_I32,       /* one signed LEB128 of 32 bits */
  WASM_IMM_I64        /* one signed LEB128 of 64 bits */
};

#define WASM_OPS(X)                           \
  X(OP_BLOCK, 0x02, WASM_IMM_BLOCKTYPE)       \
  X(OP_LOOP, 0x03, WASM_IMM_BLOCKTYPE)        \
  X(OP_IF, 0x04, WASM_IMM_BLOCKTYPE)          \
  X(OP_ELSE, 0x05, WASM_IMM_NONE)             \
  X(OP_END, 0x0B, WASM_IMM_NONE)              \
  X(OP_BR, 0x0C, WASM_IMM_LABEL)              \
  X(OP_BR_IF, 0x0D, WASM_IMM_LABEL)           \
  X(OP_BR_TABLE, 0x0E, WASM_IMM_LABELS)       \
  X(OP_RETURN, 0x0F, WASM_IMM_NONE)           \
  X(OP_CALL, 0x10, WASM_IMM_INDEX)            \
  X(OP_SELECT, 0x1B, WASM_IMM_NONE)           \
  X(OP_LOCAL_GET, 0x20, WASM_IMM_INDEX)       \
  X(OP_LOCAL_SET, 0x21, WASM_IMM_INDEX)       \
  X(OP_LOCAL_TEE, 0x22, WASM_IMM_INDEX)       \
  X(OP_GLOBAL_GET, 0x23, WASM_IMM_INDEX)      \
  X(OP_GLOBAL_SET, 0x24, WASM_IMM_INDEX)      \
  X(OP_I64_LOAD, 0x29, WASM_IMM_MEMARG)       \
  X(OP_I64_STORE, 0x37, WASM_IMM_MEMARG)      \
  X(OP_I32_CONST, 0x41, WASM_IMM_I32)         \
  X(OP_I64_CONST, 0x42, WASM_IMM_I64)         \
  X(OP_I64_EQZ, 0x50, WASM_IMM_NONE)          \
  X(OP_I64_EQ, 0x51, WASM_IMM_NONE)           \
  X(OP_I64_LT_U, 0x54, WASM_IMM_NONE)         \
  X(OP_I64_LE_U, 0x58, WASM_IMM_NONE)         \
  X(OP_I64_GE_U, 0x5A, WASM_IMM_NONE)         \
  X(OP_I64_ADD, 0x7C, WASM_IMM_NONE)          \
  X(OP_I64_SUB, 0x7D, WASM_IMM_NONE)          \
  X(OP_I64_MUL, 0x7E, WASM_IMM_NONE)          \
  X(OP_I64_DIV_U, 0x80, WASM_IMM_NONE)        \
  X(OP_I64_REM_U, 0x82, WASM_IMM_NONE)        \
  X(OP_I64_OR, 0x84, WASM_IMM_NONE)           \
  X(OP_I32_WRAP_I64, 0xA7, WASM_IMM_NONE)     \
  X(OP_I64_EXTEND_I32_U, 0xAD, WASM_IMM_NONE)

#endif
