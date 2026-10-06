// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Extract the known-answer vectors from proofs/agda/ExactCounts/Vectors.agda into
// proofs/vectors/vectors.toml, which test/test_proof_vectors.jl reproduces against the
// shipped Julia functions.
//
// Run it only after the gate has passed (proofs/check.sh does this): a vector is
// evidence because Agda accepted it, so extracting from a tree that does not
// type-check would publish numbers nobody verified.
//
// It also copies the certified rounding table in proofs/agda/ExactCounts/Sweep.agda
// to proofs/vectors/sweep.toml.
//
//   bun proofs/extract-vectors.js          write vectors.toml and sweep.toml
//   bun proofs/extract-vectors.js --check  fail if either file on disk is stale
//
// Every `vec-*` signature must match one of the shapes below.  One that does not
// is an error, never a silent omission, so the vector count in the output is the
// vector count in the proof.  Integers are written as strings because several
// exceed 2^53 and TOML integers stop at 2^63 - 1.

import { readFileSync, writeFileSync, existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const PROOFS = dirname(fileURLToPath(import.meta.url));
const SOURCE = join(PROOFS, "agda", "ExactCounts", "Vectors.agda");
const ENTRY = join(PROOFS, "agda", "ExactCounts", "All.agda");
const OUTPUT = join(PROOFS, "vectors", "vectors.toml");
const SWEEP_SOURCE = join(PROOFS, "agda", "ExactCounts", "Sweep.agda");
const SWEEP_OUTPUT = join(PROOFS, "vectors", "sweep.toml");

/** Remove Agda line comments and nested block comments, keeping line structure. */
function stripComments(text) {
  let out = "";
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text.startsWith("{-", i) && !text.startsWith("{-#", i)) { depth++; i++; continue; }
    if (depth > 0 && text.startsWith("-}", i)) { depth--; i++; continue; }
    if (depth > 0) { if (text[i] === "\n") out += "\n"; continue; }
    if (text.startsWith("--", i)) { while (i < text.length && text[i] !== "\n") i++; out += "\n"; continue; }
    out += text[i];
  }
  return out;
}

/** Read an Agda integer literal, `+ n` or `-[1+ n ]`, as a BigInt; null if it is neither. */
function agdaInt(s) {
  let m = s.match(/^\(?\s*\+\s+(\d+)\s*\)?$/);
  if (m) return BigInt(m[1]);
  m = s.match(/^\(?\s*-\[1\+\s+(\d+)\s*\]\s*\)?$/);
  if (m) return -(BigInt(m[1]) + 1n);
  return null;
}

const INT = String.raw`(\(\s*\+\s+\d+\s*\)|\(\s*-\[1\+\s+\d+\s*\]\s*\))`;
const NAT = String.raw`(\d+)`;

// Each shape turns one signature into one record.  Denominators in the Agda are
// stored as "one less than": `IsRounding n d …` divides by d+1 and `mkℚᵘ p q` is
// p/(q+1), so the records hold the real denominator and the Julia side never
// has to know the encoding.
const SHAPES = [
  {
    re: new RegExp(`^(IsRoundHalfAway|IsRoundHalfUp|IsRounding) ${INT} ${NAT} ${NAT} ${INT}$`),
    make: (m) => ({
      kind: { IsRoundHalfAway: "round_half_away", IsRoundHalfUp: "round_half_up", IsRounding: "round_half_down" }[m[1]],
      numerator: agdaInt(m[2]), denominator: BigInt(m[3]) + 1n,
      digits: BigInt(m[4]), scaled: agdaInt(m[5]),
    }),
  },
  {
    re: new RegExp(`^relativeAbundance ${NAT} ${NAT} ≡ value \\(mkℚᵘ ${INT} ${NAT}\\)$`),
    make: (m) => ({
      kind: "abundance", count: BigInt(m[1]), total: BigInt(m[2]),
      numerator: agdaInt(m[3]), denominator: BigInt(m[4]) + 1n,
    }),
  },
  {
    re: new RegExp(`^relativeAbundance ${NAT} ${NAT} ≡ refused (zeroTotal|countExceedsTotal)$`),
    make: (m) => ({ kind: "abundance_refused", count: BigInt(m[1]), total: BigInt(m[2]), refusal: m[3] }),
  },
  {
    re: new RegExp(`^(True|False) \\(fits\\? ${NAT} ${INT}\\)$`),
    make: (m) => ({ kind: "fits", fits: m[1] === "True", bits: BigInt(m[2]) + 1n, value: agdaInt(m[3]) }),
  },
  {
    re: new RegExp(`^result \\(checkedSumOf (.*)\\) ≡ (ok ${INT}|refused overflow)$`),
    make: (m) => {
      const terms = [...m[1].matchAll(new RegExp(`bnd ${NAT} ${INT}`, "g"))];
      const widths = new Set(terms.map((t) => t[1]));
      const shape = m[1].replace(new RegExp(`bnd ${NAT} ${INT}`, "g"), "B");
      if (widths.size !== 1 || !/^\(B\) \(B( ∷ B)* ∷ \[\]\)$/.test(shape)) return null;
      return {
        kind: "checked_sum", bits: BigInt([...widths][0]) + 1n,
        terms: terms.map((t) => agdaInt(t[2])),
        ...(m[2].startsWith("ok") ? { sum: agdaInt(m[3]) } : { refusal: "overflow" }),
      };
    },
  },
];

/** Parse every `vec-*` signature in the vectors module; throw on any it cannot read. */
function extract() {
  if (!/^import ExactCounts\.Vectors$/m.test(stripComments(readFileSync(ENTRY, "utf8")))) {
    throw new Error("ExactCounts/All.agda does not import ExactCounts.Vectors: the vectors would be unchecked");
  }
  const lines = stripComments(readFileSync(SOURCE, "utf8")).split("\n");
  const records = [];
  const defined = new Set();
  for (const line of lines) {
    const def = line.match(/^(vec-\S+) =/);
    if (def) { defined.add(def[1]); continue; }
    const sig = line.match(/^(vec-\S+) : (.+?)\s*$/);
    if (!sig) {
      if (/^vec-/.test(line)) throw new Error(`unreadable vec- line: ${line}`);
      continue;
    }
    let rec = null;
    for (const { re, make } of SHAPES) {
      const m = sig[2].match(re);
      if (m && (rec = make(m))) break;
    }
    if (!rec) throw new Error(`${sig[1]}: signature matches no known shape: ${sig[2]}`);
    records.push({ name: sig[1], ...rec });
  }
  for (const r of records) {
    if (!defined.has(r.name)) throw new Error(`${r.name} has a signature but no definition`);
  }
  if (records.length === 0) throw new Error("no vectors found");
  return records;
}

/** Render one TOML value: integers and BigInts as decimal strings, arrays elementwise. */
function tomlValue(v) {
  if (typeof v === "bigint") return JSON.stringify(v.toString());
  if (Array.isArray(v)) return `[${v.map(tomlValue).join(", ")}]`;
  return JSON.stringify(v);
}

/** Render the records as the TOML file test/test_proof_vectors.jl reads. */
function render(records) {
  const head = [
    "# SPDX-License-Identifier: MPL-2.0",
    "# GENERATED by proofs/extract-vectors.js from proofs/agda/ExactCounts/Vectors.agda.",
    "# Do not edit: change the Agda, run proofs/check.sh, then re-extract.",
    "# Integers are strings because several exceed 2^53.",
    "",
    `source = "proofs/agda/ExactCounts/Vectors.agda"`,
    `count = ${records.length}`,
  ];
  const body = records.map((r) =>
    ["", "[[vector]]", ...Object.entries(r).map(([k, v]) => `${k} = ${tomlValue(v)}`)].join("\n"));
  return head.join("\n") + "\n" + body.join("\n") + "\n";
}

/**
 * Read every row of the certified rounding table.  Throws if the gate entry point
 * does not import the table, or if a line that looks like a row cannot be read.
 */
function extractSweep() {
  if (!/^import ExactCounts\.Sweep$/m.test(stripComments(readFileSync(ENTRY, "utf8")))) {
    throw new Error("ExactCounts/All.agda does not import ExactCounts.Sweep: the table would be unchecked");
  }
  const row = new RegExp(`^  row ${INT} ${NAT} ${NAT} ${INT} ∷$`);
  const rows = [];
  for (const line of stripComments(readFileSync(SWEEP_SOURCE, "utf8")).split("\n")) {
    if (!/^\s*row\b/.test(line)) continue;
    const m = line.match(row);
    if (!m) throw new Error(`unreadable sweep row: ${line}`);
    rows.push([agdaInt(m[1]), BigInt(m[2]) + 1n, BigInt(m[3]), agdaInt(m[4])]);
  }
  if (rows.length === 0) throw new Error("no sweep rows found");
  return rows;
}

/** Render the table as the TOML file test/test_proof_vectors.jl reads. */
function renderSweep(rows) {
  return [
    "# SPDX-License-Identifier: MPL-2.0",
    "# GENERATED by proofs/extract-vectors.js from proofs/agda/ExactCounts/Sweep.agda.",
    "# Each row is [numerator, denominator, digits, scaled]: Agda proved that",
    "# numerator/denominator rounds, halves away from zero, to scaled / 10^digits.",
    "",
    `source = "proofs/agda/ExactCounts/Sweep.agda"`,
    `count = ${rows.length}`,
    "rows = [",
    ...rows.map((r) => `  [${r.join(", ")}],`),
    "]",
    "",
  ].join("\n");
}

const outputs = [
  [OUTPUT, render(extract()), (t) => `${t.match(/^\[\[vector\]\]$/gm).length} vectors`],
  [SWEEP_OUTPUT, renderSweep(extractSweep()), (t) => `${t.match(/^count = (\d+)$/m)[1]} rows`],
];
let stale = false;
for (const [path, text, size] of outputs) {
  const name = path.slice(PROOFS.length + 1);
  if (process.argv.includes("--check")) {
    if (!existsSync(path) || readFileSync(path, "utf8") !== text) {
      console.error(`extract-vectors: ${name} is stale; run \`bun proofs/extract-vectors.js\``);
      stale = true;
    } else {
      console.log(`extract-vectors: ${name} is current (${size(text)})`);
    }
  } else {
    writeFileSync(path, text);
    console.log(`extract-vectors: wrote ${name} (${size(text)})`);
  }
}
if (stale) process.exit(1);
