;; notraptool refuses this module: an i64.div_u with no divisor guard.
(module (func (param i64 i64) (result i64) local.get 0 local.get 1 i64.div_u))
