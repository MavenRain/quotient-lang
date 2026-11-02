;; notraptool refuses this module: it has memory.grow (0x40).
(module (memory 1 1) (func (drop (memory.grow (i32.const 0)))))
