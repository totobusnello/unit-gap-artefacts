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
`z ∧ x_new` and `z ∨ x_new`. At n = 5 there are **at least fifteen** distinct classes — **eleven** in
the lift closure plus **four** non-lifts — so the family is strictly richer than its own closure and is
not one small case propagated by a construction. All fifteen are checked pairwise distinct by exhaustive
canonicalisation over the full 7680-element NPN group, in pure Python with no solver involved.

The closure holds eleven rather than six because both lift directions are counted: 6 + 6 with exactly
one collision, which happens at the single NP-self-complementary class among the six — `OR-lift(z)` is
NPN-equivalent to `AND-lift(¬z)`, so the two lifts of `z` coincide precisely when `¬z` is NP-equivalent
to `z`. The counter asserts that explanation class by class. An earlier version of this file said "at
least ten": the count was low because the counting script generated only the AND-lifts, which Kirill
Krinkin spotted on 2026-08-11 while checking these artefacts without running a solver.

**The count splits by trust path, and `VERIFY.md` states the split instead of averaging it.** Two of
the four non-lifts carry a forced-multi certificate produced with **no symmetry breaking at all**, and
those are the two whose CNF hashes are pinned in the manifest; the other two were certified through a
proved WLOG gate-ordering, for which no no-symmetry-breaking CNF exists to pin. So **`F₅ ≥ 13` needs no
symmetry-breaking argument** and `F₅ ≥ 15` additionally rests on that ordering lemma. The headline is
unaffected either way: refuting "the family is only its lift closure" needs one non-canalizing witness,
and one of the two no-symmetry-breaking witnesses is exactly that.

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
