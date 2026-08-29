# unit-gap-verify

Reproducible, machine-checkable artifacts for the unit-gap / forced-reconvergence results in
And-Inverter-Graph exact synthesis: the refutation of Theorem 7 of *The Unit Gap*
(arXiv:2603.08033) and the positive structure that replaces it — a family of gap = 1 functions
whose *every* size-optimal circuit is forced to reconverge (the **forced-reconvergence family**).

**Start with [`VERIFY.md`](VERIFY.md)** — setup, one-command reproduction, and a zero-setup
`drat-trim` spot check.

- [`proofs/`](proofs/) — the Lift Theorem (full proof) and the synthesis note (refutation →
  positive structure → non-lift classes), with honest scope.
- [`encoder/`](encoder/) — the AIG exact-synthesis SAT encoder + an independent `verify_circuit`.
- [`verify/`](verify/) — reproduction scripts, the certificate manifest (CNF SHAs), and tiny
  sample certificates.

## What is established

At n = 4 the family has exactly six NPN classes, exhaustively. The Lift Theorem (a paper proof,
corroborated by certificates at n = 4, 5 and 6) makes it non-empty at every n ≥ 4, and it covers both
`z ∧ x_new` and `z ∨ x_new`. At n = 5 there are **at least 74** distinct classes — **eleven** in
the lift closure plus **ten** non-lifts — so the family is strictly richer than its own closure and is
not one small case propagated by a construction. All 74 are checked pairwise distinct by exhaustive
canonicalisation over the full 7680-element NPN group, in pure Python with no solver involved.

The closure holds eleven rather than six because both lift directions are counted: 6 + 6 with exactly
one collision, which happens at the single NP-self-complementary class among the six — `OR-lift(z)` is
NPN-equivalent to `AND-lift(¬z)`, so the two lifts of `z` coincide precisely when `¬z` is NP-equivalent
to `z`. The counter asserts that explanation class by class. An earlier version of this file said "at
least ten": the count was low because the counting script generated only the AND-lifts, which Kirill
Krinkin spotted on 2026-08-11 while checking these artefacts without running a solver.

**All ten non-lifts carry a forced-multi certificate produced with no symmetry breaking at all**, and
their CNF hashes are pinned in the manifest. Two of them were, until 2026-08-12, certified only through
a proved WLOG gate-ordering; re-running their at-most-one-shared query with the ordering switched off
closed both — UNSAT in 214 s and 180 s, `drat-trim` `s VERIFIED`. So **`F₅ ≥ 21` needs no
symmetry-breaking argument**, and the earlier split between `F₅ ≥ 13` certified and `F₅ ≥ 15` with the
lemma is retired. Nothing in this bundle rests on that ordering. The headline never depended on it
anyway: refuting "the family is only its lift closure" needs one non-canalizing witness, and there are
ten.

Four of those ten are the cheapest members known, and they came from settling a question the earlier
counts left open: how few gates can such a function have? An edge-counting argument bounds it below —
a size-optimal circuit on `n` essential variables has `2K` input edges, of which `n + K − 1` are spent
keeping every non-output vertex alive, so two gates of fan-out ≥ 2 force `K ≥ n + 1`, hence `opt ≥ 6`
at `n = 5`. Level 6 turns out to be empty: enumerating all of its 62 400 candidates with `gap = 1`, every
single one admits a size-optimal circuit with just **one** reconvergence. Level 7 is not empty. Its
exhaustive scan yields six classes, two of which are the two lifts of the one `n = 4` class that costs
six gates — exactly what the closure theorem predicts — and four of which are new:

| class | weight | `opt` | `tree` |
|---|---|---|---|
| `0x0001aac9` | 9/32 | 7 | 8 |
| `0x0003dcde` | 13/32 | 7 | 8 |
| `0x0007a8a7` | 11/32 | 7 | 8 |
| `0x000ff3fd` | 17/32 | 7 | 8 |

Each carries its own chain with no ordering argument: `opt` by UNSAT at `k = 1..6`, every leg
`drat-trim` `s VERIFIED`, plus a re-simulated model at `k = 7`; `tree = 8` by a formula-mode UNSAT at
`k = 7` and a witness at `k = 8`; forced-multi by an at-most-one-shared UNSAT, also VERIFIED. So **the
cheapest forced-multi function with unit gap on five essential variables costs exactly seven gates**,
against `opt` of 8 or 9 for every witness held before.

Essentiality is part of the statement, not a footnote. Without it the claim is false: pad the n = 4
witness with an inert fifth variable and you get `0x03de03de`, forced-multi with unit gap at `opt = 6`,
certified on the same chain (`verify/sample_certs/n5_0x03de03de_opt_k1..4`). That function is the n = 4
phenomenon in five-variable clothing, which is what the qualifier is there to exclude.

Two things that scan does *not* establish, and the distinction matters. `F₅ ≥ 21` rests on the four
certificates alone — the enumeration is how they were found, not why they hold. And the claim that level
7 holds *exactly* six classes is the one part resting on the enumeration being complete; the bound and
the minimality do not. None of the four is balanced, so none can be NP-self-complementary, and the
count of such classes at `n = 5` stays at zero.

The fifth and sixth arrived on 2026-08-14, from applying the construction behind three of the first four
to **every** n = 4 seed instead of the one it was aimed at: eighteen constructions, each decided in two
stages (does the gap survive; if so, does forcedness). `0x07bc0514` and `0x57fd07bc` came back UNSAT at
`k = 9` with `s VERIFIED` in 3869 s and 3159 s.

**What travels and what does not.** This bundle pins four of the six certificates, with CNF and DRAT
hashes and a regenerator you can run. The two from 2026-08-14 are pinned by CNF hash only
(`b1aa73f8b28408b0`, `36fa40b5b325aa31`): their DRAT proofs are **4.5 GB and 3.9 GB**, too large to ship,
where the largest proof embedded here is 27 MB. Reproducing them means re-running the solver — about an
hour of `kissat` and another of `drat-trim` per class on one core — rather than checking a shipped proof.
We say so rather than let the count imply four hashes cover six classes. The same sweep killed five other candidates by an audited
satisfying assignment, and the split is by **seed**, not by construction: two of the six seeds preserve
forcedness in all three variants and three preserve it in none, including variants where the gap
survives. Which property of the seed decides is open.

**On rarity, the honest version:** the random census found one witness in 14,466 sampled truth tables,
and that is a **yield, not a density** — the sampler is deliberately biased toward sparse, low-cost
functions, and the bias favours discovery rather than working against it. Uniform sampling does not
repair the estimate within any budget we could afford: 40 uniform draws produced no confirmed sample in
the region where every known witness lives. `VERIFY.md` carries the measurement and the exact wording.

The core witnesses regenerate from scratch (the first n = 5 non-lift witness, the tenth class found by
random census, and the n = 4 Lift base); a few larger enumerations (the n = 4 census, the n = 6
corroboration) are cited from the full development rather than re-run here — `VERIFY.md` says exactly
which is which. Not an asymptotic or lower-bound result — a structural result and its machine-checked
certificates.
