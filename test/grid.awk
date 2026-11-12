# Reads a `langc ir` dump and prints one `NAME [ARGS...]` line for each case of
# the differential grid. A Flag parameter takes 0 and 1. A Nat parameter takes
# small values, and, when the entry has no loop, also the values at the 2^32
# and 2^64 limits (the ADD_CARRY cases). An entry with a loop gets
# only small values, because a large count runs past the evaluator fuel.
BEGIN {
  small = "0 1 2 3 5 7"
  big = small " 4294967295 4294967296 4294967297 18446744073709551615"
  n = 0
  stepsmall = "0 1 2"
  cap = 243
  sn = 0
}
# A step entry (S9 u5, Q-S9-36 (a)) ends its `func` line with the count N of
# its buffer words and the count R of its reads: `N buffer words, R reads`
# (Q-S9-38 (a)). The reads are the first R words of the buffer (Q-S9-8 (a)).
# Its case line is `@N NAME F1..Fk R1..Rr`, the step form of test/run-wasm.mjs
# (Q-S9-35 (a)). Each field and each read word takes 0, 1 and 2 (a Flag field
# takes 0 and 1). An entry gets at most `cap` cases: a slot that passes the cap
# takes only its first values.
/^func .* buffer words, [0-9]+ reads$/ {
  instep = 1
  sn++
  sname[sn] = $2
  ssig = $0
  sub(/^func [^ ]+ \(/, "", ssig)
  sub(/\).*$/, "", ssig)
  gsub(/,/, "", ssig)
  stypes[sn] = ssig
  sbuf[sn] = $(NF - 4) + 0
  sreads[sn] = $(NF - 1) + 0
  next
}
/^func / {
  instep = 0
  n++
  name[n] = $2
  sig = $0
  sub(/^func [^ ]+ \(/, "", sig)
  sub(/\).*$/, "", sig)
  gsub(/,/, "", sig)
  types[n] = sig
  loop[n] = 0
  next
}
/^ +(repeat|while) / { if (!instep) loop[n] = 1 }
END {
  for (i = 1; i <= n; i++) cases(name[i], types[i], loop[i] ? small : big)
  for (i = 1; i <= sn; i++) stepcases(i)
}
function cases(nm, ty, nats,    t, nt, k, c, nc, j, v, nv, m, out) {
  nc = 1
  c[1] = nm
  nt = split(ty, t, " ")
  for (k = 1; k <= nt; k++) {
    nv = split(t[k] == "flag" ? "0 1" : nats, v, " ")
    m = 0
    for (j = 1; j <= nc; j++) {
      for (i2 = 1; i2 <= nv; i2++) out[++m] = c[j] " " v[i2]
    }
    nc = m
    for (j = 1; j <= nc; j++) c[j] = out[j]
  }
  for (j = 1; j <= nc; j++) print c[j]
}
function stepcases(e,    ty, t, nt, k, c, nc, j, i2, v, nv, m, out) {
  ty = stypes[e]
  for (k = 1; k <= sreads[e]; k++) ty = ty " nat"
  nc = 1
  c[1] = "@" sbuf[e] " " sname[e]
  nt = split(ty, t, " ")
  for (k = 1; k <= nt; k++) {
    nv = split(t[k] == "flag" ? "0 1" : stepsmall, v, " ")
    if (nc * nv > cap) nv = int(cap / nc)
    if (nv < 1) nv = 1
    m = 0
    for (j = 1; j <= nc; j++) {
      for (i2 = 1; i2 <= nv; i2++) out[++m] = c[j] " " v[i2]
    }
    nc = m
    for (j = 1; j <= nc; j++) c[j] = out[j]
  }
  for (j = 1; j <= nc; j++) print c[j]
}
