# The "Unit Gap" Is Base-Dependent: A Mechanically Verified Refutation and a Three-Base Census at n ≤ 4

**Status interno:** DRAFT v1 (2026-07-13). Consolida claims 7P-PNP-CLM-0024..0029 (ledger), a
formalização Lean (`../formal/UnitGap.lean`) e os censos das 3 bases (`../experiments/npn4_bases.csv`).
Revisão adversarial da refutação: 4 famílias (REV-0009..0012); do censo AIG: 2 famílias
(REV-0013/0014). Este bloco e as referências internas saem de qualquer versão pública.
Publicação/preprint SOMENTE com autorização de Luiz (10_PUBLICATION_RULES).
>
> **Correção 2026-07-17 (pós REV-0015..0018 sobre a v0 do paper):** (i) as 3 classes de gap máximo 6
> (§3) são NPN **DISTINTAS**, não "parity-4 and relatives" — parity é uma delas (opt_XAG 6/5/3, pesos
> de Hamming 6/8/8); (ii) a definição verbatim de `s` (Cor 6) do Krinkin é `|D_a∩D_b|`=3, e o paper é
> internamente inconsistente (§2 usa `opt` nos filhos vs §3 Bellman `(Tv)(f)=min(1+v(a)+v(b))`
> recursivo); (iii) `tree(⊕₃)≥9` é `native_decide`, não kernel `decide`. Estas e as demais correções
> (~20) vivem na **v1 do paper** (`../drafts/paper1_unitgap_basedep_v1.md`); esta technote é a base
> histórica, não reescrita.

---

## Abstract

Krinkin's *The Unit Gap* (arXiv:2603.08033) asserts that for every Boolean function, minimum
formula size exceeds minimum circuit size by at most one gate (Theorem 2: gap ∈ {0,1}, in the
And-Inverter Graph cost model), with a structural corollary bounding the "sharing term" s ∈ {0,1}
(Corollary 6). We refute both. Under the paper's own verbal definition of formula (every gate has
fan-out one), parity of three variables is a counterexample: opt(⊕₃) = 6 — UNSAT at 5 gates
certified by a DRAT proof checked with drat-trim — while tree(⊕₃) = 9, giving gap 3; the optimal
6-gate circuit shares a 3-gate sub-DAG between the two children of its output gate, giving s = 3.
Khrapchenko's classical bound independently forces tree(⊕₃) ≥ 8 gates, so gap ≥ 2 survives even if
every computation above were wrong. The counterexample is formalized in Lean 4 (kernel-checked
except one `native_decide` over a finite dynamic-programming sweep). The error in the published
proof is a type confusion in the recursion for tree(f): the displayed identity minimizes
1 + opt(a) + opt(b) over decompositions, silently allowing internally-shared children inside an
object that the definition requires to be a tree. A full census over the 222 NPN classes of n = 4
shows the failure is structural, not incidental: 72/222 classes (32.4%) have gap ≥ 2, with maximum
gap 6 attained exactly by parity-4 and its two NPN relatives — where the formula lower bound
tree(⊕₄) = 15 meets Khrapchenko's bound exactly. Finally, we show the phenomenon is
**base-dependent**: repeating the census in the XOR-AND-graph (XAG) base, the unit-gap property
*holds* — gap_XAG = 0 for all 256 functions of n = 3 and gap_XAG ∈ {0,1} for all 222 classes of
n = 4. The large AIG gaps are precisely the cost of simulating linear (parity) structure in a base
without XOR; the sharing that Theorem 2 tried to bound is, at these sizes, almost entirely reuse of
linear subcircuits. A replicated MIG census (matching Soeken et al.'s published table exactly,
class by class) validates the synthesis pipeline externally.

## 1. Definitions and scope

An **AIG** over x₁..xₙ is a circuit of 2-input AND gates with free negations on edges and on the
output; size = number of gates. A **formula** (tree) is a circuit in which every gate has fan-out
one. tree(f) and opt(f) denote minimum formula and circuit size; gap(f) = tree(f) − opt(f). Both
are NPN-invariant. An **XAG** adds a native 2-input XOR gate (negations on XOR inputs normalize
away); an **MIG** uses 3-input majority gates with edge negations and constant inputs. All results
below are exhaustive for n ≤ 4 and make no claim for general n.

## 2. The refutation (n = 3)

**Theorem 2 of arXiv:2603.08033 is false under the paper's definition of formula.** The paper
defines a formula verbally as fan-out-one ("a tree") and then displays

> tree(f) = min over f = a∧b (or f̄ = a∧b) of (1 + opt(a) + opt(b)),

with **opt**, not **tree**, on the right-hand side. With opt in the children, the trivial
decomposition f = 1∧f yields tree(f) ≤ 1 + opt(f) for every f — the "theorem" is an artifact of
the identity, which measures a one-level decomposition cost, not formula size. Under the verbal
definition the recursion must be tree(f) = min (1 + tree(a) + tree(b)), and for ⊕₃:

- **opt(⊕₃) = 6.** Upper bound: explicit 6-gate circuit (two chained XOR blocks sharing the middle
  node), verified by simulation. Lower bound: UNSAT at k = 5, kissat 4.0.4, DRAT proof (147 KB)
  checked by drat-trim (`s VERIFIED`); regeneration byte-identical.
- **tree(⊕₃) = 9.** Upper bound: explicit 9-gate formula (duplicate the x₁⊕x₂ subtree), verified
  by simulation. Lower bound: exact fixed-point of the tree recursion over all 256 functions,
  independently confirmed by a layer-by-layer enumeration (new functions per cost 1..9:
  24, 64, 30, 80, 32, 0, 16, 0, 2 — the two cost-9 functions are exactly 0x96 and 0x69).
- **Analytic fail-safe.** Khrapchenko: L(⊕₃) ≥ |E|²/(|A||B|) = 144/16 = 9 leaves ⟹ ≥ 8 gates,
  so gap(⊕₃) ≥ 2 independently of both computations above.

Hence gap(⊕₃) = 3, refuting Theorem 2. **Corollary 6 (s ∈ {0,1}) is refuted directly:** in the
6-gate optimum, both children of the output gate contain the 3-gate sub-DAG computing x₁⊕x₂, so
s = 3 (structurally, and arithmetically 1 + 4 + 4 − 6 = 3, with opt of each child = 4 certified by
an UNSAT-at-3 DRAT proof). **Theorem 7** (classification of shared gates when gap = 1) loses its
proof (it depends on Corollary 6) and its universal reading is false; its conditional statement
under the standard definition is not refuted by ⊕₃ (which has gap 3) — it is left unproven.
**Theorems 3 and 4 survive**; for Theorem 3 we supply a corrected proof (the published |S| ≥ k−1
count fails when g is an input-level gate; counting input incidences instead gives 2m ≥ n + m,
i.e., m ≥ n, for every non-tree optimal circuit).

**Diagnostic signature.** In Table 1 of the paper (n = 3, complete), the two functions listed with
gap = 1 at opt = 6 decode exactly to parity and its complement — which is what the displayed
recursion (opt in the children) reports for them. Independently, GLM's review re-derived that of
the 18 functions with opt = 6 at n = 3, sixteen have true formula cost 7 and exactly two have 9.

**Verification chain.** Four independent model families (Grok/xAI, GPT-5.6/OpenAI, Kimi/Moonshot,
GLM/Zhipu) adversarially reviewed the package and sustained it, several re-deriving the numbers
from scratch (REV-0009..0012). The counterexample is formalized in Lean 4.31.0 without Mathlib
(`UnitGap.lean`): witnesses and the structural minimality lemma are kernel-checked (`decide`), the
finite DP sweep uses one `native_decide`, and the axiom footprint is audited
(`propext, Classical.choice, Quot.sound`).

## 3. The failure is structural: AIG gap census at n = 4

tree(f) for all 65,536 functions by layered DP (2.4 s, numpy; independently re-implemented as a
global Bellman fixed-point with explicit polarities — all 65,536 cells agree), joined with the
complete exact opt catalog (status `exact` enforced). Distribution of gap over the 222 NPN classes:

| gap | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| classes | 93 | 57 | 40 | 13 | 14 | 2 | 3 |

**72/222 classes (32.4%) violate gap ∈ {0,1}.** Maximum gap 6 is attained exactly by
{0x1668, 0x16e9, 0x6996} — parity-4 and relatives — with opt = 9 and tree = 15, where
Khrapchenko's bound (≥ 16 leaves ⟹ ≥ 15 gates) is met with equality. Embedded n = 3 functions
reproduce the n = 3 table 256/256. Adversarially reviewed by two further families
(REV-0013 re-derived the exact distribution; REV-0014 audited both implementations).

## 4. Base dependence: the same census in XAG and MIG

**XAG.** Encoder validated by a two-level gate (n = 2 sanity; n = 3 complete with an independent
exhaustive enumeration agreeing with the SAT route in both directions). Census of all 222 classes
(9 min): opt_XAG max = 7, strictly below AIG in 190/222 classes; opt_XAG(⊕₄) = 3. Formula sizes by
the same layered DP: tree_XAG max = 7, tree_XAG(⊕₄) = 3. The gap census:

- n = 3: **gap_XAG = 0 for all 256 functions.**
- n = 4: **gap_XAG ∈ {0,1}** — {0: 218, 1: 4} over the 222 classes.

That is: **the unit-gap property, false in AIG, holds empirically in XAG for n ≤ 4.** The large
AIG gaps are the cost of duplicating linear structure; once XOR is native, sharing buys at most one
gate at these sizes. Krinkin's structural intuition survives in the richer base at small n; the
theorem in his own base does not, and neither does its proof in any base (the recursion error is
definitional). Whether gap_XAG stays bounded for larger n is open — parity no longer separates, but
nothing here rules out other separators.

**MIG (replication as pipeline validation).** The optimal MIG sizes for all 222 classes were
published by Soeken, Amarù, Gaillardon and De Micheli (DATE 2016, Table I). We re-derived the full
census with a different solver (kissat vs Z3), a different encoding, ten years apart — and matched
the published distribution **exactly, bucket by bucket** ({0:2, 1:2, 2:5, 3:18, 4:42, 5:117, 6:35,
7:1}), including the unique 7-node class. This is reciprocal external validation: of their table,
and of the exact-synthesis pipeline used throughout this note.

**Cross-base table (n = 4, per-class in `npn4_bases.csv`):**

| | AIG | XAG | MIG |
|---|---|---|---|
| max opt | 10 | 7 | 7 |
| opt(⊕₄) / tree(⊕₄) | 9 / 15 | 3 / 3 | 6 / — |
| gap census | up to 6; 32% ≥ 2 | {0,1} | deferred |

(tree_MIG requires a ternary DP whose naive form is cubic in set sizes; deferred.)

## 5. Verification levels (explicit)

| Claim | Level |
|---|---|
| opt(⊕₃) = 6, opt of h-child = 4 (lower bounds) | DRAT-certified (drat-trim `s VERIFIED`), byte-identical regeneration |
| tree(⊕₃) = 9; witnesses | Lean 4 kernel (`decide`) for witnesses + structural lemma; DP sweep via `native_decide`; two independent implementations |
| gap(⊕₃) ≥ 2 | Analytic (Khrapchenko), independent of all computation |
| AIG gap census n = 4 | Two independent implementations + two adversarial families; opt side inherits catalog certification |
| XAG census | Gated encoder (independent exhaustive enumeration at n = 3, both directions); SAT models simulation-verified; UNSAT side kissat without DRAT (declared) |
| MIG census | Same gating + exact match with independently published table |
| Refutation package overall | 4 independent model families sustained (REV-0009..0012) |

## 6. Related work and novelty (hedged)

- **Krinkin, arXiv:2603.09379** (the NPN-4 AIG catalog; we closed its two open entries — separate
  note) and **arXiv:2603.08033** (the refuted paper). Both communicated to the author
  (krinkin/bounds#1, krinkin/unit-gap#1); no response yet as of 2026-07-13.
- **MIG:** optimal n = 4 sizes previously published (Soeken et al., DATE 2016; extended TCAD 2017).
  Our census is replication, claimed only as validation.
- **XAG total-gate count:** essentially the classical combinational complexity over the full binary
  basis B2 — every 2-input operation that depends on both inputs is one AND-with-polarities or one
  XOR — tabulated for n ≤ 4 by Knuth (TAOCP 7.1.2 / BOOLCHAINS; our max 7 agrees with the classical
  bound). We therefore claim **no novelty for the XAG numbers themselves**; per-class
  cross-validation against Knuth's data is queued.
- **Multiplicative complexity** (only ANDs counted, XOR free; Turan–Peralta and successors) is a
  different measure from total XAG gates.
- **What we believe is new:** (i) the refutation of the Unit Gap theorem and its corollary, with
  machine-checked certificates and a Lean formalization; (ii) the complete gap censuses
  (tree − opt per class) in AIG and XAG at n ≤ 4 and the resulting base-dependence observation.
  Formula-size tables at small n exist in classical literature (over B2); we have not found the
  gap-by-base analysis stated anywhere. Novelty verification for (ii) beyond the sources above is
  ongoing and this claim is correspondingly hedged.

## 7. Open questions

1. Does gap_XAG remain in {0,1} for n = 5 (or does a non-linear separator appear)?
2. Is there a clean theorem behind the empirical XAG unit gap at small n — e.g., a normal form
   argument bounding sharing when linear structure is factored out?
3. tree_MIG: an efficient exact DP (the gap column for MIG).
4. A corrected, base-relative formulation of Krinkin's Theorem 7, with proof.

## Provenance

All artifacts (encoders, gate scripts, censuses, CNFs, DRAT proofs, Lean sources, review verbatims,
call log) are versioned in the program repository. Analysis and code produced by an AI system
(Claude, Anthropic) under the direction of Luiz Antonio Busnello; certificates checked by standard
independent tools (kissat, drat-trim, Lean); mathematical claims adversarially cross-reviewed by
four independent model families before external communication.
