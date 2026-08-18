# Technote — Krinkin's Theorem 7 (Two-Mechanism) is false as stated

<!-- snapshot-stamp -->
> **Snapshot de 2026-08-07.** Esta é uma nota de trabalho: os números aqui são o estado do
> artefato NAQUELE dia e **não** são reconferidos por gate. O valor corrente de qualquer
> contagem vive no CSV que a produziu (`experiments/ [private tree]`), lido por
> `bash tools/numbers.sh`; o estágio do projeto vive em [`STATUS.md`](../../STATUS.md). Divergência entre esta nota e o artefato resolve-se **a favor do artefato**.

> **Claim `7P-PNP-CLM-0033`** (FINITE_SCOPE_VERIFIED, n=4, 2026-08-06). Short note, citable
> alongside the v4 withdrawal of arXiv:2603.08033. Follows the LASTRO standard
> (`../13_WRITEUP_STANDARD.md`). Reviewed by the pre-communication gate (Codex REV-0060 +
> Kimi REV-0061, 2026-08-06): GO after the precision fixes incorporated here.

## The statement

Krinkin, *The Unit Gap* (arXiv:2603.08033, §6), **Theorem 7 (Two-Mechanism):**

> *In any size-optimal AIG with gap(f) = 1, the sharing arises from exactly one gate
> with fan-out 2, employing either dual-polarity reuse (consumers reference the gate in
> opposite polarities) or same-polarity reuse (consumers reference the gate in the same
> polarity). No other sharing structure can produce gap = 1.*

AIG basis = 2-input AND gates, free inversions on edges and output, constant 1 free; `opt(f)`
= minimum gate count of a circuit; `tree(f)` = minimum of a formula (fan-out 1); `gap = tree −
opt`. "Sharing" = a gate with fan-out ≥ 2 (a reconvergence).

## What exactly fails (and what does NOT)

The statement makes three claims; they must be separated:

1. **Uniqueness — "exactly one gate … no other sharing structure":** **FALSE** at n=4.
2. **`s(a,b) = 1` at the top decomposition** (what the proof establishes via Cor 6): **FALSE**
   — in the witnesses, the top cut gives `s = 3`.
3. **Per-gate dichotomy — each shared gate is dual- or same-polarity reuse:** **NOT refuted**
   (it is nearly tautological: 2 consumers ⇒ equal or opposite polarities). In our witnesses
   each individual fan-out-2 gate is indeed classifiable this way.

So: **what falls is UNIQUENESS** ("exactly one", "no other structure") and the `s=1` step of
the proof — not the dual/same taxonomy. The refutation is of the statement **as written**, not
of the (correct) observation that fan-out-2 reuses come in two flavors.

## The result

Enumerating size-optimal circuits (k = opt) of the **57 NPN classes with gap=1** at n=4 —
**exhaustive on the 26 pure classes** (all-conforming or all-violating) and **until a violator
is found on the 31 mixed** ones (short-circuit; see caveat 3):

- **37/57** admit a **size-optimal** AIG with **≥ 2 fan-out-2 gates** (≥ 2 reconvergences),
  contradicting *"exactly one gate with fan-out 2"* and *"no other sharing structure"*.
- **6 are "zero-conforming"** (**exhaustive** enumeration): `0x0358, 0x0359, 0x03de, 0x06b5,
  0x07bc, 0x178e` — **every** optimal circuit has ≥ 2 reconvergences; **no** circuit conforming
  to the theorem exists. The other 31 of the "37" are mixed (they have both a conforming and a
  violating optimum).
- Every observed violation is of the "≥ 2 fan-out-2 gates" type — **none** is fan-out ≥ 3.

**Canonical witness — `0x03de`** (opt = 6, tree = 7, gap = 1): the **12 normalized optimal
models** (in the encoder's convention) are all multi-share. One of them (verified by simulation
over the 16 rows):
```
g1 = x1 ∧ ¬x2       g4 = ¬g2 ∧ ¬g3      (g2, g3 have fan-out 2)
g2 = ¬x2 ∧ ¬x3      g5 = g2 ∧ g3
g3 = ¬x4 ∧ ¬g1      g6 = ¬g4 ∧ ¬g5   (output)
```
`g2` and `g3` have fan-out 2. The cones of the two output operands (g4, g5) intersect in
`{g1, g2, g3}` ⇒ **top cut `s(a,b) = 3`**, not 1. `opt = 6` certified by DRAT.

**Alternative DRAT witness — `0x0016`** (opt = 7, tree = 8, gap = 1; **mixed** class — also has
conforming optima): the 7-gate optimal AIG with g2, g3 of fan-out 2 (also top cut `s = 3`), in
`thm7_witness.json`.

## The proof of the theorem also falls

The published proof of Theorem 7 says *"By Corollary 6, gap = 1 implies s(a,b) = 1 at some
decomposition: exactly one gate g is shared between the two child sub-DAGs"* — and **Corollary
6 has already been refuted** (claim `0025`: `s` reaches 3 in ⊕₃ and 6 in ⊕₄). Moreover, the
`s = 1` step fails directly: at the top of the exhibited circuits (0x03de above; likewise
0x0016), `s(a,b) = 3`.

## Ledger (lastro)

- **Enumeration:** `experiments/exp_krinkin_cor6/thm7_check.py` — exact-synthesis SAT encoder
  (`exp_gate_0001/aig_exact.py`, validated in G3), enumeration via blocking clauses,
  `verify_circuit` (simulation over the 16 rows) on **every** circuit before classifying
  (REV-0004). `thm7_results.json`.
- **DRAT (opt):** `opt(0x0016) = 7` (UNSAT k=1..6) and `opt(0x03de) = 6` (UNSAT k=1..5), each
  CNF with a kissat proof verified by `drat-trim` (`s VERIFIED`); SHA-256 (16-hex prefix) in
  `thm7_witness.json` / `thm7_witness_0x03de.json`. The full `k=1..opt−1` UNSAT chain establishes
  the opt lower bound.
- **DRAT (tree) — `0x03de`:** `tree(0x03de) = 7` DRAT-certified (**formula** encoder, fan-out 1,
  UNSAT k=1..6 `s VERIFIED`, + a 7-gate tree witness; `gen_drat_tree_0x03de.py`,
  `tree_witness_0x03de.json`). The formula encoder was validated against the census/DP on
  functions of known tree size before use. **Hence, for the flagship witness `0x03de`,
  `gap = tree − opt = 7 − 6 = 1` is DRAT end-to-end — it does NOT depend on the census.** The
  whole counterexample is moreover hand-checkable (the optimal circuit simulates `0x03de` over
  the 16 rows and exhibits 2 reconvergences).
- **Independent fan-out recount** of the 6 zero-conforming classes: `revalidate_zero_conforme.py`
  (fan-out recomputed by separate code; reuses encoder/Glucose) — 6/6 OK. Not a fully independent
  revalidation (encoder and solver are the same); what is independent is the fan-out count.
- **Lean formalization (n=4):** `formal/ThresholdTreeN4.lean` certifies Krinkin's Theorems 3 and
  4 (the surviving ones) by `native_decide` — not this result, but the same scope.
- **Adversarial panel — 4 families, ALL SUSTAINED** (REV-0056..0059) + **pre-communication gate**
  (REV-0060 Codex, REV-0061 Kimi): GO after fixes. Human review: Luiz Antonio Busnello.

## Caveats (declared)

1. **`opt` DRAT-certified only for `0x0016` and `0x03de`.** For the other 4 zero-conforming and
   the 31 mixed classes, `opt` is **census-backed** (claim `0026`, dual tree-DP + exact-synthesis
   of opt); the 6 zero-conforming have a `k−1` UNSAT consistency check (Glucose), which is not, by
   itself, an independent optimality proof. If the census `opt` were overestimated on a mixed
   class, its "optimal violator" might not be optimal — hence the **strong** witnesses are the DRAT
   ones.
2. **`gap = 1` (tree side):** for the flagship **`0x03de` it is DRAT-certified** (tree=7 via the
   formula encoder, above) — independent of the census. For the other witnesses, the tree side
   still rests on the dual-DP census (0026) + an independent Bellman DP re-derived in the panel
   (REV-0058/GLM).
3. **The 31 "mixed" classes were not enumerated exhaustively** (short-circuit upon finding both a
   conforming and a violating optimum); the *existence* of a violator in them is solid, but their
   counts are prefixes. The **26 pure** classes (6 zero-conforming + 20 all-conforming) **were**
   exhaustive.
4. The encoder→CNF link is a semantic bridge not covered by DRAT (mitigated by G3 + MIG, claim
   `0029`).
5. Refutes the statement **as written** (global uniqueness). The per-gate dual/same taxonomy is
   NOT touched (see "what does not fail").

## Context

Third refutation of the same paper, all certified: **Theorem 2** (Unit Gap, claim `0024`),
**Corollary 6** (Decomposition, claim `0025`), and now **Theorem 7**. **Theorems 3 and 4**
(Threshold, Tree) remain sustained (🔵 n≤4, now with a Lean certificate). The v4 arXiv withdrawal
(2026-08-04) already credits L. A. Busnello + Zenodo DOI `10.5281/zenodo.21630762`. A positive
follow-up (claim `0034`, `technote_thm7_substitution.md`) shows no clean structural repair of
Theorem 7 exists at n=4.
