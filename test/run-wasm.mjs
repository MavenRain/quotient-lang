// Runs entries of a langc Wasm module and prints each result as `langc eval`
// does: a number, or `trap` when the module traps.
// Usage: node test/run-wasm.mjs FILE NAME [ARGS...]
//        node test/run-wasm.mjs FILE -   (one `NAME [ARGS...]` line on stdin per call)
// A step call (S9 u5, Q-S9-35 (a)) is the line `@N step_X F1..Fk R1..Rr`. N is
// the count of the buffer words of the entry, k is the parameter count of the
// export, and the R words after the fields are the reads. Before the call, the
// host writes read word I at byte 8I of `memory` and fills each of the
// W = N - R write words with the poison word 0xA5A5A5A5A5A5A5A5. It prints the
// form of `langc eval`: the flag, then for flag 1 each write word (`-` for a
// poison word). A flag 0 with a changed write word prints `0 dirty`.
import { readFileSync } from "node:fs";

const [file, name, ...args] = process.argv.slice(2);
if (file === undefined || name === undefined) {
  process.stderr.write("usage: node test/run-wasm.mjs FILE NAME [ARGS...] | FILE -\n");
  process.exit(2);
}
const instance = new WebAssembly.Instance(new WebAssembly.Module(readFileSync(file)), {});
const poison = 0xa5a5a5a5a5a5a5a5n;

const entryOf = (entry) => {
  const fn = instance.exports[entry];
  if (typeof fn !== "function") throw new Error(`no exported entry '${entry}'`);
  return fn;
};

const run = (fn, words) => {
  try {
    return BigInt.asUintN(64, BigInt(fn(...words.map(BigInt))));
  } catch (e) {
    if (e instanceof WebAssembly.RuntimeError) return "trap";
    throw e;
  }
};

const word = (i) => new DataView(instance.exports.memory.buffer).getBigUint64(8 * i, true);
const put = (i, v) => new DataView(instance.exports.memory.buffer).setBigUint64(8 * i, v, true);

const stepCall = (n, [entry, ...words]) => {
  const fn = entryOf(entry);
  const reads = words.slice(fn.length).map((w) => BigInt.asUintN(64, BigInt(w)));
  const writeSlots = Array.from({ length: Math.max(n - reads.length, 0) }, (_, j) => reads.length + j);
  reads.forEach((v, i) => put(i, v));
  writeSlots.forEach((i) => put(i, poison));
  const flag = run(fn, words.slice(0, fn.length));
  const writes = writeSlots.map((i) => word(i));
  return flag === "trap"
    ? flag
    : flag === 0n
      ? (writes.some((w) => w !== poison) ? "0 dirty" : "0")
      : [flag.toString(), ...writes.map((w) => (w === poison ? "-" : w.toString()))].join(" ");
};

const plainCall = ([entry, ...words]) => {
  const r = run(entryOf(entry), words);
  return r === "trap" ? r : r.toString();
};

const call = ([head, ...rest]) =>
  head.startsWith("@") ? stepCall(Number(head.slice(1)), rest) : plainCall([head, ...rest]);

const calls = name === "-"
  ? readFileSync(0, "utf8").split("\n").filter((line) => line !== "").map((line) => line.split(" "))
  : [[name, ...args]];
process.stdout.write(calls.map((c) => call(c) + "\n").join(""));
