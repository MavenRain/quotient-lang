;; The dirty module of the gate (S9 u5, Q-S9-39 (a)). It is not langc
;; output. It has the step ABI of test/ir/step.lang: the export step_Pay
;; takes 2 fields, and the buffer at byte 0 of `memory` has 4 words (2 reads,
;; then 2 write words). It writes write word 0 (buffer word 2, byte 16) and
;; gives the flag 0. A correct step entry stores no write word on the flag 0,
;; so test/run-wasm.mjs must print `0 dirty` for this module.
(module
  (memory (export "memory") 1 1)
  (func (export "step_Pay") (param i64 i64) (result i64)
    (i64.store (i32.const 16) (i64.const 0))
    (i64.const 0)))
