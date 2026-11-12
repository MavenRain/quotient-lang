#!/bin/sh
# The kit gate. `make check` runs it from the kit directory after the build.
set -eu
fail=0
count=0
# kit LIST FILE prints --kit when FILE is a line of LIST. A row whose text uses a
# kit name or a Nat or word literal is a kit row (orbit-lang S3); the others run
# in guest mode.
kit() {
  if [ -f "$1" ] && rg -q -x -F "$2" "$1"; then echo --kit; fi
}
for prog in examples/*.lang; do
  out=$(build/langc $(kit examples/kit.txt "${prog#examples/}") check "$prog" 2>&1) || true
  count=$((count + 1))
  if [ "$out" != "ok" ]; then
    echo "FAIL $prog: $out"
    fail=$((fail + 1))
  fi
done
echo "examples: $count checked, $fail failed"

tmp=${TMPDIR:-/tmp}/langc-gate.$$
mkdir -p "$tmp"
awk 'BEGIN { printf "def deep : Nat := " } { } END {
  for (i = 0; i < 1100; i++) printf "("; printf "1"; for (i = 0; i < 1100; i++) printf ")"; print "" }' </dev/null >"$tmp/deep.lang"

# refusals DIR LABEL: each line of DIR/expect.txt is `FILE CODE`. `langc check`
# must exit 1 and print `langc: CODE: ...` on stderr.
refusals() {
  checked=0
  while read -r file code; do
    path="$1/$file"
    [ "$file" = "deep.lang" ] && path="$tmp/deep.lang"
    status=0
    build/langc $(kit "$1/kit.txt" "$file") check "$path" 2>"$tmp/err" >/dev/null || status=$?
    first=$(head -n 1 "$tmp/err")
    checked=$((checked + 1))
    case "$status:$first" in
      "1:langc: $code: "*) ;;
      *) echo "FAIL $file: want exit 1 and $code, got exit $status: $first"; fail=$((fail + 1)) ;;
    esac
  done <"$1/expect.txt"
  echo "$2 refusals: $checked checked"
}
refusals test/parse parse
refusals test/check check

# A REFUSE_KIT row refuses a kit item in guest mode only: `langc --kit check`
# must print ok.
kit_only=0
while read -r file code; do
  [ "$code" = "REFUSE_KIT" ] || continue
  status=0
  out=$(build/langc --kit check "test/check/$file" 2>&1) || status=$?
  kit_only=$((kit_only + 1))
  if [ "$status:$out" != "0:ok" ]; then
    echo "FAIL $file: want ok under --kit, got exit $status: $out"
    fail=$((fail + 1))
  fi
done <test/check/expect.txt
echo "kit-only refusals: $kit_only checked"

# A refl refusal shows both normal forms.
build/langc $(kit test/check/kit.txt bad-refl.lang) check test/check/bad-refl.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'the path at i1 is some 1201, but the type needs some 1200' "$tmp/err"; then
  echo "FAIL bad-refl.lang: the message does not show both normal forms"
  fail=$((fail + 1))
fi

# A REFUSE_TIME refusal names the op-count form (S3, O3).
time_hint=0
build/langc $(kit test/check/kit.txt time-block.lang) check test/check/time-block.lang 2>"$tmp/err" >/dev/null || true
time_hint=$((time_hint + 1))
if ! rg -q -F 'count operations: a position is `len r` (an OpPos) and a deadline is a count of later operations' "$tmp/err"; then
  echo "FAIL time-block.lang: the message does not name the op-count form"
  fail=$((fail + 1))
fi

# A higher-order Asset is refused at the slot, not later at valueBal (S2,
# USER ruling Q-S2-5 (a)): rule_value_count gives the same code.
build/langc check test/check/sig-asset-higher.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Asset: the slot Asset must be first-order data' "$tmp/err"; then
  echo "FAIL sig-asset-higher.lang: the message does not name the Asset slot"
  fail=$((fail + 1))
fi
build/langc check test/check/sig-key-higher.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Key: the slot Key must be first-order data' "$tmp/err"; then
  echo "FAIL sig-key-higher.lang: the message does not name the Key slot"
  fail=$((fail + 1))
fi
# The auth slots (S4, USER rulings Q-S4-1 (a), Q-S4-2 (a) and Q-S4-6 (a)):
# Witness is first-order data, Body does not mention Witness, and
# witnessOk has the kernel-fixed type.
build/langc check test/check/witness-higher.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Witness: the slot Witness must be first-order data' "$tmp/err"; then
  echo "FAIL witness-higher.lang: the message does not name the Witness slot"
  fail=$((fail + 1))
fi
build/langc check test/check/body-has-witness.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Body: the slot Body must not mention Witness' "$tmp/err"; then
  echo "FAIL body-has-witness.lang: the message does not name the Body slot"
  fail=$((fail + 1))
fi
build/langc check test/check/witnessok-type.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'witnessOk: witnessOk must have the type Body -> Witness -> Sum Unit Unit' "$tmp/err"; then
  echo "FAIL witnessok-type.lang: the message does not name the witnessOk type"
  fail=$((fail + 1))
fi
# The Digest slot and txid (S4, USER rulings Q-S4-2 (a), Q-S4-3 (a) and
# Q-S4-8 (a)): Digest is first-order data, and txid has the type Body ->
# Digest.
build/langc check test/check/digest-higher.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Digest: the slot Digest must be first-order data' "$tmp/err"; then
  echo "FAIL digest-higher.lang: the message does not name the Digest slot"
  fail=$((fail + 1))
fi
build/langc check test/check/txid-reads-witness.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'txid: txid must have the type Body -> Digest' "$tmp/err"; then
  echo "FAIL txid-reads-witness.lang: the message does not name the txid type"
  fail=$((fail + 1))
fi
build/langc check test/check/txid-authtx.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'txid: txid must have the type Body -> Digest' "$tmp/err"; then
  echo "FAIL txid-authtx.lang: the message does not name the txid type"
  fail=$((fail + 1))
fi
# The Sig slot and agg (S4, USER rulings Q-S4-4 (a) and Q-S4-6 (a)): agg
# at Bag Sig needs sigComm, the commutative clause (law L1).
build/langc check test/check/sig-no-comm.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'Sig: agg at Bag Sig needs sigComm, the commutative clause (law L1, O2)' "$tmp/err"; then
  echo "FAIL sig-no-comm.lang: the message does not name the sigComm clause"
  fail=$((fail + 1))
fi
build/langc check test/check/sig-comm-wrong.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'sigComm: agg at Bag Sig needs sigComm, the commutative clause (law L1, O2)' "$tmp/err"; then
  echo "FAIL sig-comm-wrong.lang: the message does not name the sigComm clause"
  fail=$((fail + 1))
fi
# The QC prelude (S4, USER ruling Q-S4-5 (a)): quorum must have the type
# Pfin Node -> Sum Unit Unit.
build/langc check test/check/qc-quorum-wrong.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'quorum: quorum must have the type Pfin Node -> Sum Unit Unit' "$tmp/err"; then
  echo "FAIL qc-quorum-wrong.lang: the message does not name the quorum type"
  fail=$((fail + 1))
fi
# A fold out of Pfin without the idem case names the pfinIdem case (S3,
# law L2, USER ruling Q-S2-4 (a)).
build/langc check test/check/pfin-no-idem.lang 2>"$tmp/err" >/dev/null || true
if ! rg -q -F 'the pfinIdem case is the idempotent clause (law L2)' "$tmp/err"; then
  echo "FAIL pfin-no-idem.lang: the message does not name the pfinIdem case"
  fail=$((fail + 1))
fi
echo "time hint: $time_hint checked"

# Each line of test/eval/expect.txt is `FILE NAME [ARGS] => OUTPUT`. `langc eval`
# must exit 0 and print OUTPUT.
evals=0
while IFS= read -r line; do
  want=${line#* => }
  set -- ${line%% => *}
  file=$1
  name=$2
  shift 2
  status=0
  got=$(build/langc $(kit examples/kit.txt "$file.lang") eval "examples/$file.lang" "$name" "$@" 2>"$tmp/err") || status=$?
  first=$(head -n 1 "$tmp/err")
  evals=$((evals + 1))
  case "$status|$got|$first" in
    "0|$want|"*) ;;
    *) echo "FAIL eval $file $name: want $want, got exit $status: $got $first"; fail=$((fail + 1)) ;;
  esac
done <test/eval/expect.txt
echo "evals: $evals checked"

# eval_refused STATUS CODE NAME [ARGS]: `langc --kit eval examples/entries.lang
# NAME ARGS` must exit STATUS and print `langc: CODE: NAME: ...` on stderr.
eval_refused() {
  want_status=$1
  code=$2
  shift 2
  status=0
  build/langc --kit eval examples/entries.lang "$@" 2>"$tmp/err" >/dev/null || status=$?
  case "$status:$(head -n 1 "$tmp/err")" in
    "$want_status:langc: $code: $1: "*) ;;
    *) echo "FAIL eval $*: want exit $want_status and $code, got exit $status"; fail=$((fail + 1)) ;;
  esac
}
eval_refused 2 EVAL_ARGS addPrice 1
eval_refused 2 EVAL_ARGS addPrice x 1
eval_refused 2 EVAL_ARGS addPrice 18446744073709551616 1
eval_refused 2 EVAL_ARGS pick 2 4 9
eval_refused 1 EVAL_ENTRY nope

# step_eval STATUS WANT FILE NAME [ARGS]: the step form of `langc --kit eval`
# (S9). The arguments of a step are the fields of the family, then the values
# of its reads. With STATUS 0 the command must exit 0 and print WANT (the
# flag, then the value of each write). With an other STATUS the command must
# exit STATUS and print `langc: WANT: NAME: ...` on stderr.
stepevals=0
step_eval() {
  want_status=$1
  want=$2
  shift 2
  status=0
  got=$(build/langc --kit eval "$@" 2>"$tmp/err") || status=$?
  first=$(head -n 1 "$tmp/err")
  stepevals=$((stepevals + 1))
  case "$want_status:$status:$got:$first" in
    "0:0:$want:") ;;
    "$want_status:$want_status::langc: $want: $2: "*) ;;
    *) echo "FAIL step eval $*: want exit $want_status and $want, got exit $status: $got $first"; fail=$((fail + 1)) ;;
  esac
}
step_eval 0 "1 6 5" test/ir/step.lang step_Pay 3 4 5 6
step_eval 0 "0" test/ir/step.lang step_Pay 3 4 0 6
step_eval 0 "1 5 5" test/ir/step.lang step_Pay 3 4 5 0
step_eval 0 "1 65535" examples/step-ok.lang step_Pay 1 2 65535 8 9
step_eval 2 EVAL_ARGS examples/step-ok.lang step_Pay 1 2 65536 8 9
step_eval 2 EVAL_ARGS test/ir/step.lang step_Pay 3 4 5
step_eval 2 EVAL_ARGS test/ir/step.lang step_Pay x 4 5 6
step_eval 2 EVAL_ARGS test/ir/step.lang step_Pay 3 4 5 abc
echo "step evals: $stepevals checked"

# The target (S3). The Wasm writer is in the build: `langc build
# examples/functions.lang` must exit 0 and write a module that wasm-validate
# accepts.
builds=0
status=0
build/langc $(kit examples/kit.txt functions.lang) build examples/functions.lang -o "$tmp/functions.wasm" 2>"$tmp/err" || status=$?
builds=$((builds + 1))
if [ "$status" -ne 0 ] || ! wasm-validate "$tmp/functions.wasm" 2>>"$tmp/err"; then
  echo "FAIL build functions: want exit 0 and a valid module, got exit $status: $(head -n 1 "$tmp/err")"
  fail=$((fail + 1))
fi
echo "builds: $builds checked"

# The IR (S3): `langc ir examples/functions.lang` must exit 0 and give one
# func line for each line of `langc abi`.
irs=0
status=0
build/langc $(kit examples/kit.txt functions.lang) ir examples/functions.lang >"$tmp/ir.txt" 2>"$tmp/ir.err" || status=$?
irs=$((irs + 1))
funcs=$(rg -c '^func ' "$tmp/ir.txt" || echo 0)
entries=$(build/langc $(kit examples/kit.txt functions.lang) abi examples/functions.lang | rg -c '.' || echo 0)
[ "$status" -eq 0 ] && [ "$funcs" -gt 0 ] && [ "$funcs" -eq "$entries" ] || { echo "FAIL ir functions: exit $status, $funcs funcs for $entries entries: $(head -n 1 "$tmp/ir.err")"; fail=$((fail + 1)); }
echo "ir: $irs lowered"

# The IR refusals (S3): `langc --kit check` must accept each file, and
# `langc --kit ir` must exit 1 and print `langc: ` and the given text first.
# closure.lang gives a function value at run time (REFUSE_RUNTIME_CLOSURE).
# kmap.lang uses a KMap operation at run time (a refuse() arm of lower.c).
# tree.lang folds a tree that exists only at run time (REFUSE_RUNTIME_TREE).
# spine.lang walks lists that exist only at run time, so its heap use has no
# static bound (S3).
# step-val.lang has a step and a `Val` that is not Nat, Amount, Flag or Size
# (S9: a step entry reads and writes each `Val` as one word).
# test/ir/step-memory.lang has a definition with the name of the memory
# export of a step module (S9 u3b, Q-S9-21 (a)).
irrefusals=0
ir_refused() {
  status=0
  build/langc --kit check "test/ir/$1" > /dev/null 2>&1 || status=$?
  [ "$status" -eq 0 ] || { echo "FAIL $1: check exit $status"; fail=$((fail + 1)); }
  status=0
  first=$(build/langc --kit ir "test/ir/$1" 2>&1 > /dev/null) || status=$?
  case "$status:$first" in
    "1:langc: $2"*) ;;
    *) echo "FAIL $1: want exit 1 and $2, got exit $status: $first"; fail=$((fail + 1)) ;;
  esac
  irrefusals=$((irrefusals + 1))
}
ir_refused closure.lang "REFUSE_RUNTIME_CLOSURE: bad: "
ir_refused kmap.lang "REFUSE_LOWER: got: the Wasm host does not lower an elim, KMap"
ir_refused tree.lang "REFUSE_RUNTIME_TREE: tips: "
ir_refused step-val.lang "REFUSE_LOWER: step_Pay: the Wasm host does not lower a step when the type Val is not Nat, Amount, Flag or Size"
ir_refused step-memory.lang "REFUSE_LOWER: step_Pay: a definition has the name of the memory export"
ir_refused spine.lang "REFUSE_LOWER: trapHead: heap use has no static bound"
ir_refused hop.lang "REFUSE_LOWER: hopDepth: a recursive fold over a block of families"
echo "ir refusals: $irrefusals checked"

# The Ind matrix (S5 unit 5, Q-S5-32 (a)). Each line of test/ind/expect.txt is
# `NAME ROW`: `langc --kit ind` of examples/ind-*.lang and test/ind/*.lang must
# exit 0 and print the rows of NAME.lang in the file order. A refused program
# stays refused, and a program with no footprint family prints no row.
: >"$tmp/ind.txt"
for prog in examples/ind-*.lang test/ind/*.lang; do
  name=$(basename "$prog" .lang)
  status=0
  build/langc --kit ind "$prog" >"$tmp/ind.one" 2>"$tmp/err" || status=$?
  [ "$status" -eq 0 ] || { echo "FAIL ind $name: want exit 0, got exit $status: $(head -n 1 "$tmp/err")"; fail=$((fail + 1)); }
  awk -v n="$name" '{print n " " $0}' "$tmp/ind.one" >>"$tmp/ind.txt"
done
cmp -s "$tmp/ind.txt" test/ind/expect.txt || { echo "FAIL ind rows: the rows are not the rows of test/ind/expect.txt"; fail=$((fail + 1)); }
indrows=$(awk 'END {print NR}' "$tmp/ind.txt")
status=0
build/langc $(kit test/check/kit.txt step-reads-witness.lang) ind test/check/step-reads-witness.lang >"$tmp/ind.one" 2>"$tmp/err" || status=$?
case "$status:$(head -n 1 "$tmp/err")" in
  "1:langc: REFUSE_WITNESS_READ: "*) ;;
  *) echo "FAIL ind step-reads-witness: want exit 1 and REFUSE_WITNESS_READ, got exit $status"; fail=$((fail + 1)) ;;
esac
if [ -s "$tmp/ind.one" ]; then
  echo "FAIL ind step-reads-witness: a refused program printed a row"
  fail=$((fail + 1))
fi
status=0
build/langc $(kit examples/kit.txt functions.lang) ind examples/functions.lang >"$tmp/ind.one" 2>"$tmp/err" || status=$?
[ "$status" -eq 0 ] && [ ! -s "$tmp/ind.one" ] || { echo "FAIL ind functions: want exit 0 and no row, got exit $status"; fail=$((fail + 1)); }
indrows=$((indrows + 2))
echo "ind rows: $indrows checked"

# The IR lowerings (S3): `langc
# --kit check` must accept each file and `langc --kit ir` must exit 0. The
# IR text of natops.lang and of block.lang (S3) and of step.lang (S9: the
# step entry) must be test/ir/natops.ir, test/ir/block.ir and
# test/ir/step.ir (golden files: a change of the lowering changes the
# text).
irlowered=0
ir_lowered() {
  status=0
  build/langc --kit check "test/ir/$1" > /dev/null 2>&1 || status=$?
  [ "$status" -eq 0 ] || { echo "FAIL $1: check exit $status"; fail=$((fail + 1)); }
  status=0
  build/langc --kit ir "test/ir/$1" >"$tmp/$1.ir" 2>"$tmp/ir.err" || status=$?
  [ "$status" -eq 0 ] || { echo "FAIL $1: want ir exit 0, got exit $status: $(head -n 1 "$tmp/ir.err")"; fail=$((fail + 1)); }
  irlowered=$((irlowered + 1))
}
ir_lowered natops.lang
cmp -s "$tmp/natops.lang.ir" test/ir/natops.ir || { echo "FAIL natops.lang: the IR text is not test/ir/natops.ir"; fail=$((fail + 1)); }
ir_lowered block.lang
cmp -s "$tmp/block.lang.ir" test/ir/block.ir || { echo "FAIL block.lang: the IR text is not test/ir/block.ir"; fail=$((fail + 1)); }
ir_lowered step.lang
cmp -s "$tmp/step.lang.ir" test/ir/step.ir || { echo "FAIL step.lang: the IR text is not test/ir/step.ir"; fail=$((fail + 1)); }
echo "ir lowerings: $irlowered lowered"

# The writer (S3): `langc --kit build
# test/ir/natops.lang` must exit 0 and write a module that wasm-validate
# accepts. In `wasm-objdump -x`, memory 0 must have 1 page (minimum =
# maximum = the pages of the largest heap bound, at least 1). The module of
# examples/functions.lang (the builds rows) has 0 heap words: its memory 0
# must also have 1 page. The differential grid below runs these modules
# with node and compares their results with the evaluator.

status=0
build/langc --kit build test/ir/natops.lang -o "$tmp/natops.wasm" 2>"$tmp/err" || status=$?
if [ "$status" -ne 0 ] || ! wasm-validate "$tmp/natops.wasm" 2>>"$tmp/err"; then
  echo "FAIL build natops: want exit 0 and a valid module, got exit $status: $(head -n 1 "$tmp/err")"
  fail=$((fail + 1))
fi
# The module of test/ir/block.lang (S3): the same build
# check. The notrap row below uses it.
status=0
build/langc --kit build test/ir/block.lang -o "$tmp/block.wasm" 2>"$tmp/err" || status=$?
if [ "$status" -ne 0 ] || ! wasm-validate "$tmp/block.wasm" 2>>"$tmp/err"; then
  echo "FAIL build block: want exit 0 and a valid module, got exit $status: $(head -n 1 "$tmp/err")"
  fail=$((fail + 1))
fi
# The module of examples/state-no-history.lang (Q-S3-3 (b)): build lowers a
# state family as a plain family. The same build check; the notrap row
# below uses it, as does the differential grid.
status=0
build/langc $(kit examples/kit.txt state-no-history.lang) build examples/state-no-history.lang -o "$tmp/state-no-history.wasm" 2>"$tmp/err" || status=$?
if [ "$status" -ne 0 ] || ! wasm-validate "$tmp/state-no-history.wasm" 2>>"$tmp/err"; then
  echo "FAIL build state-no-history: want exit 0 and a valid module, got exit $status: $(head -n 1 "$tmp/err")"
  fail=$((fail + 1))
fi
for mod in natops functions; do
  wasm-objdump -x "$tmp/$mod.wasm" 2>/dev/null | rg -q -x -F ' - memory[0] pages: initial=1 max=1' ||
    { echo "FAIL $mod.wasm: memory 0 is not initial=1 max=1"; fail=$((fail + 1)); }
done
# build/notraptool (test/notraptool.c, S3) must accept the
# modules of natops.lang, block.lang, functions.lang and
# state-no-history.lang: exit 0 and no output. It fails a module with unreachable, memory.grow, an opcode that
# is not in src/wasmop.h, an i64.div_u or i64.rem_u with no divisor guard,
# a memory with no maximum or a maximum that is not the minimum, an import,
# or a second memory (S9 u6, Q-S9-41 (a)).
notrapmods=0
for mod in natops block functions state-no-history; do
  notrapmods=$((notrapmods + 1))
  status=0
  got=$(build/notraptool "$tmp/$mod.wasm" 2>&1) || status=$?
  [ "$status" -eq 0 ] && [ -z "$got" ] ||
    { echo "FAIL notrap $mod.wasm: want exit 0 and no output, got exit $status: $got"; fail=$((fail + 1)); }
done
echo "notrap modules: $notrapmods checked"
# The bad rows (S3): each line of test/notrap/bad/expect.txt is
# `NAME MESSAGE`. wat2wasm makes $tmp/NAME.wasm from test/notrap/bad/NAME.wat.
# build/notraptool must exit 1 and print the one line
# `notraptool: $tmp/NAME.wasm: MESSAGE`.
notrapbad=0
while read -r name msg; do
  notrapbad=$((notrapbad + 1))
  status=0
  got=$(wat2wasm --enable-annotations --enable-multi-memory "test/notrap/bad/$name.wat" -o "$tmp/$name.wasm" 2>&1 && build/notraptool "$tmp/$name.wasm" 2>&1) || status=$?
  [ "$status" -eq 1 ] && [ "$got" = "notraptool: $tmp/$name.wasm: $msg" ] ||
    { echo "FAIL notrap bad $name: want exit 1 and $msg, got exit $status: $got"; fail=$((fail + 1)); }
done <test/notrap/bad/expect.txt
echo "notrap bad rows: $notrapbad checked"
# The footprint bad rows (S9 u6, Q-S9-42 (a)): each line of
# test/footprint/bad.txt is `NAME OCTAL TAIL`. printf writes the bytes of
# OCTAL to $tmp/fp-NAME.wasm. `build/langc footprint` must exit 1, and its
# first stderr line must start with `langc: FOOTPRINT: -: ` and end with TAIL.
fpbad=0
while read -r name octal tail; do
  fpbad=$((fpbad + 1))
  printf "$octal" >"$tmp/fp-$name.wasm"
  status=0
  build/langc footprint "$tmp/fp-$name.wasm" >/dev/null 2>"$tmp/fp-bad.err" || status=$?
  first=$(head -n 1 "$tmp/fp-bad.err")
  case "$status:$first" in
    "1:langc: FOOTPRINT: -: "*"$tail") ;;
    *) echo "FAIL footprint bad $name: want exit 1 and FOOTPRINT ... $tail, got exit $status: $first"; fail=$((fail + 1)) ;;
  esac
done <test/footprint/bad.txt
echo "footprint bad rows: $fpbad checked"
# The kit evals of test/ir/spine.lang at 4. Each line is `NAME VALUE`.
spineevals=0
while read -r name want; do
  got=$(build/langc --kit eval test/ir/spine.lang "$name" 4 2>&1) || got="exit $?: $got"
  spineevals=$((spineevals + 1))
  [ "$got" = "$want" ] || { echo "FAIL spine $name 4: want $want, got $got"; fail=$((fail + 1)); }
done <<'EOF'
foldOnes 8
mapUp 20
bindUp 50
filterUp 3
trapHead 1
trapSum 3
filterTrap 7
bindTrap 1
sizeSum 20
sizeTrap 4
EOF
echo "spine evals: $spineevals checked"

# Run the scalar exports on the same grid as the evaluator. Option results
# stay outside the Wasm ABI in this slice.
wasms=0
fpmods=0
notrapwasms=0
cases=0
mismatches=0
stepruns=0
wasmrefused=0
stepexports=0
for f in examples/*.lang test/ir/natops.lang test/ir/block.lang test/ir/step.lang test/ir/step-empty.lang test/ir/step-pages.lang; do
  mode=$(kit examples/kit.txt "${f#examples/}")
  case "$f" in test/ir/*) mode=--kit ;; esac
  w="$tmp/$(basename "$f" .lang).wasm"
  # The step of these 4 examples has no code in the Wasm host (a Size
  # constructor or an elim in the step). `langc build` must refuse the module
  # with REFUSE_LOWER (Q-S9-12 (a)); the module has no differential row.
  case "$f" in
    examples/ledger.lang|examples/prefix.lang|examples/step-hygiene.lang|examples/step-run-maybe.lang)
      status=0
      first=$(build/langc $mode build "$f" -o "$w" 2>&1 >/dev/null) || status=$?
      case "$status:$first" in
        "1:langc: REFUSE_LOWER: step_"*) ;;
        *) echo "FAIL wasm $f: want exit 1 and REFUSE_LOWER on a step, got exit $status: $first"; fail=$((fail + 1)) ;;
      esac
      wasmrefused=$((wasmrefused + 1))
      continue ;;
  esac
  wasms=$((wasms + 1))
  if ! build/langc $mode build "$f" -o "$w" 2>"$tmp/w.err" || ! wasm-validate "$w" 2>>"$tmp/w.err"; then
    echo "FAIL wasm $f: $(head -n 1 "$tmp/w.err")"
    fail=$((fail + 1))
    continue
  fi
  # notraptool must accept each valid module of the loop (S9 u6,
  # Q-S9-40 (a)): exit 0 and no output.
  notrapwasms=$((notrapwasms + 1))
  status=0
  got=$(build/notraptool "$w" 2>&1) || status=$?
  [ "$status" -eq 0 ] && [ -z "$got" ] ||
    { echo "FAIL notrap wasm $f: want exit 0 and no output, got exit $status: $got"; fail=$((fail + 1)); }
  # The footprint section (S9 u4, Q-S9-25 to Q-S9-28 (a)): `langc footprint`
  # must exit 0 on the module, and its row lines (each line that is not a
  # family line `NAME: footprint ...`) must be the `langc ind` text of the
  # source in the mode of the build. A source with no family gives no output.
  # The notrap wasm row above checks each module with the section.
  status=0
  build/langc footprint "$w" >"$tmp/fp-out.txt" 2>"$tmp/w.err" || status=$?
  build/langc $mode ind "$f" >"$tmp/fp-ind.txt" 2>>"$tmp/w.err" || status="ind $?"
  [ -s "$tmp/fp-ind.txt" ] || [ ! -s "$tmp/fp-out.txt" ] || status="no ind rows"
  rg -v -F ': footprint ' "$tmp/fp-out.txt" >"$tmp/fp-rows.txt" || true
  if [ "$status" != 0 ] || ! cmp -s "$tmp/fp-rows.txt" "$tmp/fp-ind.txt"; then
    echo "FAIL footprint $f: want exit 0 and the rows of langc ind, got $status: $(head -n 1 "$tmp/w.err")"
    fail=$((fail + 1))
  elif [ -s "$tmp/fp-out.txt" ]; then
    fpmods=$((fpmods + 1))
  fi
  # The full text of `langc footprint` (S9 u4, the USER ruling of S9 s23).
  # The module of examples/ind-acct.lang has family lines and the only dep row
  # of the examples. Its text must be test/ir/ind-acct.footprint.txt.
  case "$f" in examples/ind-acct.lang)
    cmp -s "$tmp/fp-out.txt" test/ir/ind-acct.footprint.txt ||
      { echo "FAIL footprint $f: the text is not test/ir/ind-acct.footprint.txt"; fail=$((fail + 1)); } ;;
  esac
  if ! build/langc $mode ir "$f" >"$tmp/ir.txt" 2>"$tmp/w.err"; then
    echo "FAIL differential ir $f: $(head -n 1 "$tmp/w.err")"
    fail=$((fail + 1))
    continue
  fi
  # A module with a step entry (S9 u3, Q-S9-18 (a)): memory 0 must have its
  # expected number of pages (Q-S9-23 (a): 2 for test/ir/step-pages.lang, 1
  # for each other module), memory 0 must be the export `memory` (Q-S9-7 (a),
  # Q-S9-22 (a)), and each `step_<Family>` entry of the IR text must be a
  # function export with its name. The IR line of each step entry ends
  # with the part `N buffer words, R reads`, also for 0 words (Q-S9-29 (a),
  # Q-S9-38 (a)). A module with no
  # step entry must not export memory 0.
  wasm-objdump -x "$w" >"$tmp/w.dump" 2>/dev/null || true
  stepnames=$(awk '/^func step_.* buffer words, [0-9]+ reads$/ { print $2 }' "$tmp/ir.txt")
  if [ -n "$stepnames" ]; then
    stepexports=$((stepexports + 1))
    pages=1
    case "$f" in test/ir/step-pages.lang) pages=2 ;; esac
    rg -q -x -F " - memory[0] pages: initial=$pages max=$pages" "$tmp/w.dump" ||
      { echo "FAIL step export $f: memory 0 is not initial=$pages max=$pages"; fail=$((fail + 1)); }
    rg -q -x -F ' - memory[0] -> "memory"' "$tmp/w.dump" ||
      { echo "FAIL step export $f: memory 0 is not the export memory"; fail=$((fail + 1)); }
    for name in $stepnames; do
      rg -q -x " - func\[[0-9]+\] <$name> -> \"$name\"" "$tmp/w.dump" ||
        { echo "FAIL step export $f: $name is not a function export"; fail=$((fail + 1)); }
    done
  elif rg -q -F ' - memory[0] -> ' "$tmp/w.dump"; then
    echo "FAIL step export $f: a module with no step entry exports memory 0"
    fail=$((fail + 1))
  fi
  # A step case `@N NAME ARGS` (S9 u5, Q-S9-35 (a)) goes to test/run-wasm.mjs
  # as it is, and to `langc eval` without its `@N` word.
  awk -f test/grid.awk "$tmp/ir.txt" >"$tmp/cases.txt"
  : >"$tmp/want.txt"
  while read -r call; do
    status=0
    want=$(build/langc $mode eval "$f" ${call#@* } 2>/dev/null) || status=$?
    [ "$status" -eq 0 ] || want="eval-exit-$status"
    echo "$want" >>"$tmp/want.txt"
  done <"$tmp/cases.txt"
  if ! node test/run-wasm.mjs "$w" - <"$tmp/cases.txt" >"$tmp/got.txt" 2>"$tmp/w.err"; then
    echo "FAIL node $f: $(head -n 1 "$tmp/w.err")"
    fail=$((fail + 1))
    continue
  fi
  cases=$((cases + $(rg -c '.' "$tmp/cases.txt" || echo 0)))
  stepruns=$((stepruns + $(rg -c '^@' "$tmp/cases.txt" || echo 0)))
  paste -d '|' "$tmp/cases.txt" "$tmp/want.txt" "$tmp/got.txt" | awk -F '|' '$2 != $3' >"$tmp/bad.txt"
  bad=$(rg -c '.' "$tmp/bad.txt" || echo 0)
  mismatches=$((mismatches + bad))
  [ "$bad" -eq 0 ] || { echo "FAIL differential $f: $bad mismatches, first $(head -n 1 "$tmp/bad.txt")"; fail=$((fail + 1)); }
done
# The code of the module of test/ir/step.lang (S9 u3, Q-S9-20 (a)): the
# `wasm-objdump -d` text, with no offset column and no byte column, must be
# test/ir/step.wasm.txt. It shows the heap reset of the step entry and the
# byte offset of each buffer word.
wasm-objdump -d "$tmp/step.wasm" 2>/dev/null |
  awk 'p { if ($0 ~ /^[0-9a-f]+ func/) sub(/^[0-9a-f]+ /, ""); if ($0 ~ / [|] /) sub(/^.* [|] /, " "); print } /^Code Disassembly:/ { p = 1 }' >"$tmp/step.wasm.txt"
cmp -s "$tmp/step.wasm.txt" test/ir/step.wasm.txt || { echo "FAIL step.lang: the code text of the module is not test/ir/step.wasm.txt"; fail=$((fail + 1)); }
# The pair row of test/ir/step.lang (S9 u5, Q-S9-37 (a)): 2 Pay steps on 4
# different accounts, so the ind-if of `Pay Pay` holds. Each order of the 2
# steps must give the same end state. The state has 4 words, [5, 0, 7, 9].
# The call `@4 step_Pay F T S[F] S[T]` of test/run-wasm.mjs gives `1 W0 W1`,
# then S[F] := W0 and S[T] := W1. Each order must give [5, 5, 9, 7].
pair_pay() {
  printf '@4 step_Pay %s %s %s %s\n' "$1" "$2" "$3" "$4" | node test/run-wasm.mjs "$tmp/step.wasm" - 2>/dev/null
}
pair_state() {
  pst0=5
  pst1=0
  pst2=7
  pst3=9
  for pstep in "$@"; do
    case "$pstep" in
      01) pres=$(pair_pay 0 1 "$pst0" "$pst1") || pres="exit $?" ;;
      *) pres=$(pair_pay 2 3 "$pst2" "$pst3") || pres="exit $?" ;;
    esac
    set -- $pres
    [ "${1:-}" = 1 ] || { echo "step $pstep gives $pres"; return 0; }
    case "$pstep" in
      01) pst0=${2:-} pst1=${3:-} ;;
      *) pst2=${2:-} pst3=${3:-} ;;
    esac
  done
  echo "$pst0 $pst1 $pst2 $pst3"
}
pairab=$(pair_state 01 23)
pairba=$(pair_state 23 01)
case "$pairab:$pairba" in
  "5 5 9 7:5 5 9 7") ;;
  *) echo "FAIL pair step.lang: the 2 orders give $pairab and $pairba, want 5 5 9 7 for each"; fail=$((fail + 1)) ;;
esac
# The dirty row (S9 u5, Q-S9-39 (a)). A langc step entry stores no write
# word when its flag is 0, so no langc module reaches the `0 dirty` compare
# of test/run-wasm.mjs. test/ir/step-dirty.wat has the step ABI of
# test/ir/step.lang (2 fields, 2 reads, 4 buffer words); it writes write
# word 0 (buffer word 2) and gives the flag 0. The host must print `0 dirty`.
if wat2wasm test/ir/step-dirty.wat -o "$tmp/step-dirty.wasm" 2>"$tmp/w.err"; then
  dirty=$(printf '@4 step_Pay 0 1 5 0\n' | node test/run-wasm.mjs "$tmp/step-dirty.wasm" - 2>/dev/null) || dirty="exit $?"
else
  dirty="wat2wasm: $(head -n 1 "$tmp/w.err")"
fi
[ "$dirty" = "0 dirty" ] || { echo "FAIL dirty step-dirty.wat: test/run-wasm.mjs gives $dirty, want 0 dirty"; fail=$((fail + 1)); }
echo "wasm: $wasms modules valid"
echo "notrap wasm modules: $notrapwasms checked"
echo "wasm refusals: $wasmrefused refused"
echo "step exports: $stepexports checked"
echo "footprint modules: $fpmods checked"
echo "differential: $cases cases, $mismatches mismatches"
echo "step runs: $stepruns checked"
# The R0 boundary normalizes each nonzero Flag word to true.
got=$(node test/run-wasm.mjs "$tmp/natops.wasm" flagPick 2 4 9 2>&1) || got="exit $?: $got"
[ "$got" = 4 ] || { echo "FAIL wasm flagPick 2 4 9: want 4, got $got"; fail=$((fail + 1)); }

status=0
build/langc 2>/dev/null || status=$?
[ "$status" -eq 2 ] || { echo "FAIL usage: want exit 2, got $status"; fail=$((fail + 1)); }
status=0
build/langc --kit 2>/dev/null || status=$?
[ "$status" -eq 2 ] || { echo "FAIL usage --kit: want exit 2, got $status"; fail=$((fail + 1)); }
status=0
build/langc check "$tmp/missing.lang" 2>/dev/null || status=$?
[ "$status" -eq 2 ] || { echo "FAIL missing file: want exit 2, got $status"; fail=$((fail + 1)); }
rm -rf "$tmp"

# design/DESIGN.md is verbatim and can hold a dash (as leaf-lang and permit-lang).
if rg -n -g '!design/DESIGN.md' '\x{2013}|\x{2014}' . >/dev/null; then
  echo "FAIL: an em-dash or en-dash is in the kit"
  fail=$((fail + 1))
fi
echo "gate: $fail failures"
[ "$fail" -eq 0 ]
