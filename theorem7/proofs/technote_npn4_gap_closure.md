# Closing the Last Two Unresolved Entries of the NPN-4 Exact AIG Size Catalog: opt(0x1669) = opt(0x166b) = 10

**Status interno:** DRAFT v2 (2026-07-11) — v1 revisada por REV-0007 (Codex/GPT-5.6, NEEDS_REVISION,
14 findings, todos adjudicados; registro em `../../07_MODEL_CALL_LOG.md`). Este bloco de status e as
referências internas saem de qualquer versão pública. Publicação/preprint SOMENTE com autorização de
Luiz (10_PUBLICATION_RULES).

---

## Abstract

Krinkin's public catalog of exact And-Inverter Graph (AIG) circuit sizes for the 222 NPN equivalence
classes of 4-variable Boolean functions (arXiv:2603.09379) left exactly two classes unresolved —
`0x1669` and `0x166b`, each with a certified upper bound of 10 gates and a SAT-solver timeout at
gate count 9. We close both entries: **opt(0x1669) = opt(0x166b) = 10**. The lower bounds rest on a
normalization lemma (every minimum-size AIG can be brought into the normal form our encoding
searches) together with DRAT-certified UNSAT results at every gate count k = 1..9 — the k = 9
proofs (4,785,094,117 and 3,871,475,211 bytes) generated and checked on two machines, the k = 1..8
proofs (up to 204 MB) checked with the same toolchain. The upper bounds are witnessed by explicit 10-gate
circuits verified by exhaustive simulation. With the two entries settled, re-running the catalog's
own verification script extends its exact-exact mutation-edge set from 987 to 995 edges, and the
paper's Lipschitz bound (|Δopt| ≤ n) holds on all of them, with the maximum observed difference
unchanged at 4 = n.

## 1. Background

An AIG (And-Inverter Graph) over inputs x1..xn is a circuit of 2-input AND gates with free
inversions on edges and on the output; its size is the number of AND gates. NPN classification
groups the 65,536 4-variable Boolean functions into 222 equivalence classes under input
negation/permutation and output negation (hence "NPN"), with AIG size invariant within a class.
Krinkin (arXiv:2603.09379, March 2026) published SAT-derived exact sizes for 220 of the 222
classes, using the dataset to verify a Lipschitz-type bound on circuit-size change under one-bit
truth-table perturbation. For the remaining two classes — NPN representatives `0x1669` (tt = 5737)
and `0x166b` (tt = 5739) — the catalog records status `improved_ub`: a 10-gate upper bound, with
the decision at k = 9 timing out.

This note reports the closure of both entries, relative to that catalog snapshot. Priority was
checked on 2026-07-11 as follows: the arXiv entry remains at v1; the data repository
(github.com/krinkin/bounds) has no commits since 2026-03-10 and no issues or PRs; the Semantic
Scholar citations endpoint returns an empty list; targeted web searches (queries archived
internally) returned nothing beyond the paper itself. We found no prior publication of these
values; this conclusion is explicitly subject to the fact that we did not systematically sweep the
older exact-synthesis literature (e.g., ABC/mockturtle-era artifacts), where the values could exist
implicitly under a different normalization.

## 2. Method

### 2.1 Encoding and normalization lemma

We encode, as a CNF formula, the question "does a **normalized** AIG with exactly k AND gates
computing f exist?", in the standard SAT-based exact synthesis style. Nodes 1..n are inputs; node
n+i is gate i. Each gate i selects, via one-hot selection variables, an option (a, pa, b, pb):
operands a < b among the preceding nodes (so the two fan-ins are distinct nodes), with edge
polarities pa, pb ∈ {0, 1}. The gate computes (val(a) ⊕ pa) ∧ (val(b) ⊕ pb); value variables
v[i][t] encode gate outputs per truth-table row t. **Normal form imposed by the constraints:**
(N1) fan-ins are distinct nodes (a < b); (N2) no two gates select the same option tuple
(a, pa, b, pb); (N3) every gate except the last feeds some later gate; (N4) the output is the last
gate, with a free output polarity. At k = 9 the formula has 1,273 variables and 133,909 clauses; at
k = 10, 1,601 variables and 194,307 clauses.

UNSAT at k therefore refutes the existence of a *normalized* k-gate AIG. The bridge to opt values
is:

**Normalization lemma.** *If f is computable by an AIG with m ≥ 1 gates, and m = opt(f), then f is
computable by an AIG with exactly m gates satisfying (N1)–(N4).* Proof sketch: take a minimum
m-gate AIG for f. (N1): a gate whose two fan-ins are the same node u computes, depending on its two
polarities, either the literal u ⊕ p (equal polarities) or the constant 0 (opposite polarities); in
either case the gate can be eliminated — redirect each of its fanouts to u with polarity adjusted,
or propagate the constant and simplify — yielding a strictly smaller AIG for f (constants and
literals need 0 gates, and free edge/output inversions absorb the polarity), contradicting
minimality. (N2): if two gates select the same tuple they compute the same function; redirect every
fanout of the later one to the earlier one (if the later one is the output, make the earlier one
the output — same function, output polarity unchanged) and prune it — again strictly smaller,
contradiction. (N3): a gate feeding nothing and not the output is pruned — contradiction. (N4):
topologically order gates with the output gate last; the encoding's option space allows any
topological order. ∎

Consequently, UNSAT of the k = m formula refutes opt(f) = m, for every m ≥ 1. (k = 0 is excluded
directly: neither function is a constant or a literal.) The certified lower-bound chain for this
note is: **normalization lemma + DRAT-verified UNSAT at every k = 1..9 + the catalog-independent
10-gate witnesses**, giving opt ∉ {1..9} and opt ≤ 10. Every UNSAT in the chain carries a DRAT
proof checked by drat-trim; no step relies on an unverified solver answer.

**Symmetry breaking soundness.** (N2) is the only constraint beyond the textbook encoding; as shown
above it is sound for deciding opt = k. It was added for the k = 9 probes and the full validation
suite (Section 2.2) was re-run after the change.

### 2.2 Validation of the encoder (before touching the open classes)

DRAT certifies the CNF, not the encoding: an UNSAT proof shows the formula has no model, not that
the formula means "no normalized k-gate AIG computes f". The encoder was therefore validated
semantically, against solver-independent references:

- **Exhaustive cross-check (n = 2):** optimal sizes from the pipeline match an independent
  exhaustive enumerator on all 16 2-variable functions.
- **Bidirectional cross-check (n = 3, k ≤ 3):** 126 reachable functions match; 130 functions
  unreachable by the enumerator confirmed UNSAT by the encoder at k = 1..3.
- **Reproduction of a solved entry:** class `0x0016` reproduced at opt = 7 — SAT at k = 7 with the
  witness circuit verified by simulation, UNSAT at k = 6 with a DRAT proof verified by drat-trim.
- Every SAT model found anywhere in the pipeline is decoded into a circuit and re-simulated against
  the full truth table before being accepted (this check caught a real encoder bug — a collision
  between constant node values and DIMACS literal ±1 — in an early run; the bug was fixed and all
  validations re-run).

### 2.3 Toolchain and hardware

kissat 4.0.4 (macOS host: Homebrew build; EPYC host: built from source); drat-trim built from
source on each machine (macOS build: upstream commit 2e3b2dc; the EPYC build's exact commit was not
recorded — a provenance gap we note rather than paper over). Python 3.14.3 with PySAT (Glucose4)
for the small-scale validation harness. Machines: an Apple-silicon macOS host (arm64) and an AMD
EPYC 4564P server (16 cores, 124 GB RAM, Ubuntu 24.04). Decision runs (no proof logging) and
certification runs (proof logging on) are separate executions.

## 3. Results

### 3.1 Lower bounds: UNSAT at k = 9 with DRAT proofs checked on two machines

| class | decision (Mac, no proof) | proof run (EPYC) | DRAT size (bytes) | drat-trim | Mac-proof SHA-256 |
|---|---|---|---|---|---|
| 0x1669 | UNSAT, 1,543 s | UNSAT, 1,350 s | 4,785,094,117 (≈4.79 GB) | `s VERIFIED` on both machines (1,462 s Mac / 1,558 s EPYC) | `49e125a3…f8d7762` |
| 0x166b | UNSAT, 1,269 s | UNSAT, 1,115 s | 3,871,475,211 (≈3.87 GB) | `s VERIFIED` on both machines (1,389 s Mac / 1,345 s EPYC) | `10ebb75c…c0e6dd51` |

Each machine generated a proof with its own kissat build and checked it with its own drat-trim
build. These are separate runs and builds on two architectures — not independent methodological
replications: encoder, CNF, solver family/version, and checker implementation are shared. drat-trim
core statistics (Mac runs): 0x1669 — 12,162,375 of 20,591,176 lemmas in core, 82,413 of 133,909
clauses in core; 0x166b — 10,679,089 of 17,445,110 lemmas in core, 81,585 of 133,909 clauses in
core. CNF files: 1,781,704 bytes each; SHA-256
`ae822d229081d3c888de86275c6373060bdd4f43c8f9cfaa8c0a507d0df87d1a` (0x1669),
`3e66960696edf4cbdf2b5e83d6bff388a8ca297b160bb803570b912b478ca64f` (0x166b).

**Certified sweep k = 1..8.** The same encoder returns UNSAT at every gate count from 1 to 8 for
both classes, each run with proof logging and checked by drat-trim (`s VERIFIED`, 16 of 16). Proof
sizes grow from KBs to 203.6 MB (0x166b, k = 8) and 170.4 MB (0x1669, k = 8); per-proof SHA-256
hashes are archived. At k = 8 the formula has 993 variables and 89,495 clauses. Via the
normalization lemma these certified results rule out opt = m for every m ≤ 8.

### 3.2 Upper bounds: explicit 10-gate witnesses

Truth-table convention: bit t of the 16-bit integer is f on the input row where xj = bit j−1 of t
(x1 is the least-significant bit of the row index). Gate i is written (a, pa, b, pb) and computes
(val(a) ⊕ pa) ∧ (val(b) ⊕ pb) — pa = 1 means the fan-in from node a is inverted; nodes 1–4 are
x1..x4, node 4+i is gate i; the output is the last gate, non-inverted in both witnesses:

```
0x1669 (tt=5737): [(3,0,4,0),(3,1,4,1),(1,1,2,1),(2,0,5,1),(1,0,8,0),
                   (7,1,9,1),(5,1,6,1),(10,0,11,1),(10,1,11,0),(12,1,13,1)]
0x166b (tt=5739): [(2,0,3,0),(2,1,3,1),(1,0,6,1),(5,1,6,1),(4,1,8,0),
                   (4,0,8,1),(9,1,10,1),(1,1,11,1),(7,0,9,1),(12,1,13,1)]
```

Both circuits were found by kissat on the k = 10 formula (11 s and 275 s) and verified by
exhaustive simulation over all 16 rows twice: by the pipeline's built-in decoder/simulator
(`aig_exact.py`), and by a second simulator written independently of the pipeline for the review
pass (a 15-line direct evaluation of the tuple list; both agree on tt = 5737 and 5739).

### 3.3 Effect on the catalog and on the perturbation-bound verification

Marking the two classes `exact` completes the NPN-4 AIG catalog (222/222). Re-running the
catalog's own verification script (`scripts/verify_all.py`, unmodified, on the 2-line-patched CSV
and the author's published mutation graph — run archived internally with hashes and full output)
extends the script's exact-exact mutation-edge set from 987 to **995 edges, with the bound
|Δopt| ≤ n holding on all of them**. The |Δopt| distribution becomes |0| = 301, |1| = 421,
|2| = 221, |3| = 45, |4| = 7; the seven tight edges (|Δopt| = 4 = n) are unchanged. Edge
construction, canonicalization and counting are the author's script's, which we did not modify;
"gap-free" here means: every edge of the author's published mutation graph now joins two classes
with exact values, and his bound check passes on all of them.

## 4. Limitations

Finite-scope result: two specific NPN classes, in the AIG basis, under the catalog's cost model
(2-input AND gates, free inversions, size = AND-gate count). Nothing asymptotic follows. The values
are as strong as the verification chain: the normalization lemma (paper-and-pencil, stated in
§2.1), semantic validation of the encoder at small scales, and solver-independent DRAT checking at
every k = 1..9; the encoder itself is not formally verified. Timings are single-run wall-clock
times, not benchmarks.

## 5. Provenance and reproducibility

This work was produced within an AI-assisted research program led by Luiz Antonio Busnello: the encoding,
scripts, runs, and cross-checks were produced by an AI system (Claude, Anthropic) under human
direction. Proofs were generated by kissat and checked by drat-trim — the checker is the trust
anchor — on two machines. All scripts are deterministic Python; UNSAT verdicts and proof
*existence* are reproducible from the archived CNFs (proof generation ≈20–25 minutes per class on
one modern core, checking a further ≈23–26 minutes), but byte-identical proofs are **not**
guaranteed across builds/platforms — indeed the two machines' proofs differ, and only the macOS
proofs' hashes were retained. Archived internally: CNFs with hashes, proof hashes (macOS runs),
drat-trim outputs from both machines, all run scripts, and the `verify_all.py` rerun (patched CSV
diff, script snapshot, full output, hashes). Available on request.

## References

1. K. Krinkin. *A Simple Constructive Bound on Circuit Size Change Under Truth Table Perturbation.*
   arXiv:2603.09379, March 2026. Data: github.com/krinkin/bounds.
2. A. Biere, M. Fleury, N. Froleyks, M. Heule. kissat SAT solver (version 4.0.4).
3. N. Wetzler, M. Heule, W. Hunt. *DRAT-trim: Efficient Checking and Trimming Using Expressive
   Clausal Proofs.* SAT 2014. Implementation: github.com/marijnheule/drat-trim.
4. Programa 7_PROBLEMS, registros internos: `12_EXPERIMENTS.md [private tree]` (EXP-GATE-0001,
   EXP-PROBE-0001), `experiments/exp_verify_rerun/ [private tree]`, claims 7P-PNP-CLM-0021/0022/0023.
