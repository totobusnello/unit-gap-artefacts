# VERIFY — reproduce and machine-check the results

This is a self-contained guide to independently verify the unit-gap / forced-reconvergence
results in this repository. It relies only on public tools and this repo; every machine-checkable
claim can be **regenerated from scratch and re-checked**, not merely trusted.

**Principle: reproducibility, not blobs.** Some proof files are large (a DRAT proof can be
hundreds of MB), so we do not ship them. Instead we ship the encoder, a one-command regenerator,
and the pinned **CNF SHA** of each instance. A CNF's hash is deterministic from the encoder
(machine-independent); a DRAT's bytes depend on the solver build, so the portable check is
"`drat-trim` reports **VERIFIED**", together with the CNF SHA identifying the instance.

## What is claimed (honest scope)

- Krinkin's Theorem 7 (a unit gap comes from *exactly one* shared gate) is **false**; the opposite
  holds and is *forced*: some functions have **every** size-optimal AIG carrying ≥ 2 reconvergent
  (fan-out ≥ 2) gates. At n = 4 there are exactly six such NPN classes.
- **Closure / Lift Theorem** (paper proof, `proofs/proof_lift_lemma.md`): if `z` is
  forced-multi with gap = 1, so are `z ∧ x_new` and `z ∨ x_new` — hence the family exists for
  every n ≥ 4. Corroborated by DRAT at n = 4, 5, 6.
- **Density**: at n = 5 the family exceeds its own lift closure — witness `f = 0x03de ∧ (¬x₀ ∨ x₄)`
  (`0x03de0154`): non-canalizing, opt = 8, tree = 9 (gap = 1), forced-multi. Counting NPN classes,
  n = 5 has **at least ten** — six lifts plus **four non-lifts** — checked exhaustively over the full
  NPN group. So the family is a genuine object, not one small case propagated by a construction.

A **tenth class** (`0x09c50800`) completes the count, and it is the interesting one: every earlier
witness came from a directed sweep on one family, while this one fell out of a random census. See
*A tenth class, and where it came from* below.

This is a structural result in exact circuit synthesis — **not asymptotic, not a lower bound.**

## Setup (a few minutes)

Two binaries on your `PATH`: `kissat` (SAT solver + DRAT) and `drat-trim` (DRAT checker).

```sh
git clone https://github.com/arminbiere/kissat   && ( cd kissat   && ./configure && make )   # -> build/kissat
git clone https://github.com/marijnheule/drat-trim && ( cd drat-trim && make )                # -> drat-trim
# put both on PATH
```

For the pseudo-Boolean layer as well (optional — only needed for the certified-ordering method
paper, not for the results above), `tools/setup-veripb.sh` builds the full toolchain
(VeriPB 3.0 + RoundingSat + drat-trim + kissat).

## Reproduce the headline witness

```sh
python3 verify/reproduce_witness.py           # quick (~seconds): opt lower bound (k=1..7 UNSAT,
                                                     #   drat-trim VERIFIED), opt & tree SAT witnesses
                                                     #   (verify_circuit self-certifying), non-canalizing
python3 verify/reproduce_witness.py --full     # also the forced-multi no-SB certificate
                                                     #   (247 MB DRAT, ~minutes; ZERO symmetry breaking)
```

The script prints the SHA of each regenerated CNF; compare against `verify/manifest.csv`
(claim → leg → CNF SHA → verdict). The forced-multi leg's CNF SHA is pinned there
(`ed3b8350f72f8078`) and regenerates byte-identically on any machine.

**Zero-setup spot check** (only `drat-trim` needed): committed sample certificates for the opt
lower bound, k = 1..4, live in `verify/sample_certs/`:

```sh
drat-trim verify/sample_certs/n5_0x03de0154_opt_k3.cnf \
          verify/sample_certs/n5_0x03de0154_opt_k3.drat   # expect: s VERIFIED
```

## Count the classes (F₅ ≥ 10)

```sh
python3 verify/npn_check_f5.py
```

Pure Python, no solver: canonicalizes all ten witnesses over the full n = 5 NPN group (all 7680
transforms) and confirms ten distinct classes. The count prints **decomposed by provenance** — six
lifts, three from a directed sweep, one from a random census — because that split, not the total, is
the substance of the density claim.

## A tenth class, and where it came from

The tenth witness is **`0x09c50800`**. Reproduce it through the same script:

```sh
python3 verify/reproduce_witness.py 0x09c50800          # opt-LB + witnesses + non-canalizing
python3 verify/reproduce_witness.py 0x09c50800 --full   # + forced-multi no-SB (~400 MB DRAT)
```

Same legs, same trust path, no symmetry breaking anywhere: opt = 8 (UNSAT k = 1..7 with DRAT, plus a
k = 8 SAT witness `verify_circuit` confirms), tree = 9 (fan-out-1 formula at k = 9 whose per-gate
fan-out is counted, not assumed), forced-multi (at-most-one-shared UNSAT at k = 8, `drat-trim`
VERIFIED), non-canalizing. Its CNF SHAs are pinned in `verify/manifest.csv` alongside the
established witness.

What makes it worth its own section: every earlier witness came from a **directed sweep** on the
`0x03de` family — we knew where to look — while this one fell out of a **random census** of 14,466
truth tables, with no such knowledge. Existence-by-construction and existence-by-accident are
evidence of different kinds, and the family having both is what the tenth class contributes. The
count going 9 → 10 is the less interesting half.

**One in 14,466 is a yield, not a density — and the distinction is not pedantic here.** The census
sampler is *deliberately* biased toward sparse truth tables, so it over-represents low `opt`. Reading
a biased sampling rate as a density is a documented error (Ghosh & Kadelka, arXiv:2606.05196: the
parameterisation-to-function map is many-to-one, so parameter-uniform sampling is not
function-uniform).

The obvious fix — sample uniformly instead — runs into an obstruction we can state exactly, so it is
worth separating **what was measured** from **what it suggests**.

**Measured.** Of 40 uniformly random n = 5 truth tables
(`verify/density_uniform_w0*.csv`, kissat, cap 90 s per k, 76 min of CPU):
**39 did not resolve `opt` within the cap** and 1 resolved to `opt > 8`. So **zero of 40 were confirmed
to lie in `opt ≤ 8`** — the range holding every known witness (`opt ∈ 6..8`).

**Not measured, and stated as inference.** The 39 are *undecided*, not proved to exceed 8: a larger cap
or a different solver could settle some of them. So this is not a proof that the typical uniform
function has high `opt`, and "uniform sampling cannot work" would overstate it. What the numbers do
support is narrower and still decisive for the method: **under this encoder and this cap, uniform
sampling produced no usable sample in the conditioning event at all** — so a conditional density on
`opt ≤ 8` cannot be estimated this way, whatever the true distribution is. The reading we favour, and
label as a reading, is that the family sits in the tractable tail of the `opt` distribution; that would
explain why a low-`opt`-biased sampler found one, and it is a hypothesis this measurement motivates
rather than establishes.

So what is claimed here is **reachability without construction**, which the witness proves, and an
**observed yield under a declared sampler**. Not a density, and not an extrapolation to exact F₅.

## The proofs (self-contained, English)

- `proofs/proof_lift_lemma.md` — the Lift Theorem (restriction / gate-elimination).
- `proofs/unit_gap_synthesis.md` — the full synthesis (Theorem 7 refutation → positive
  structure → density), with the honest scope.
- `proofs/technote_thm7_refutation.md`, `technote_z_generalization.md`,
  `technote_npn4_gap_closure.md`, `technote_unitgap_basedep.md` — the supporting technotes.

## The encoder (what the CNFs mean)

- `encoder/aig_exact.py` — the AIG exact-synthesis SAT encoder
  (2-input AND gates, free edge/output inversions; `formula=True` = fan-out-1 formula mode) plus an
  independent `verify_circuit` (simulates a decoded circuit against the full truth table — this is
  what makes every SAT witness self-certifying, per the encoder-vs-CNF caveat).
- `encoder/n5_forced_test.py` — `build_amo_shared` (the at-most-one-shared
  "forced multiple reconvergence" encoding), used with **no symmetry breaking** on the trusted path.

## Trust boundary

The trusted path uses **no symmetry breaking**: the forced-multi certificate above is plain DRAT
over the vetted encoder, `drat-trim`-verified. (A faster gate-ordering variant exists for
convenience runs; it is a WLOG-ordering, not on the trusted path, and its machine-certified
dominance version is future work.) Each SAT witness is confirmed by `verify_circuit` independently
of the SAT solver, so the encoder→CNF translation is checked semantically, not assumed.

Two limits of `verify_circuit` worth stating, because both were live gaps until an external review
pointed them out:

- It re-simulates the truth table and **nothing else**. For a *formula* witness that is not enough —
  fan-out-1 is the whole point of the `tree` leg, and it comes from the encoding, not from the
  simulation. The tree leg therefore now decodes the model and **counts fan-out per gate**.
- A `drat-trim` run is only evidence when its status line reads exactly `s VERIFIED`. The string
  `s NOT VERIFIED` contains `VERIFIED`, so a substring test passes a *failed* proof. Check the
  status line and the exit code, never a substring.

  If you script that check, note that `drat-trim` writes its progress using **carriage returns**, so
  `s VERIFIED` does not begin a physical line: `grep -E "^s "` finds nothing, while
  `grep "s VERIFIED"` works. In Python, `text=True` plus `splitlines()` handles it; on raw bytes you
  must split on `\r` as well as `\n`.

The single step in the chain that is an argument rather than a certificate is the **lower** bound
`tree ≥ opt + 1`. It runs: forced-multi means every size-optimal circuit has ≥ 2 reconvergent gates;
a fan-out-1 formula has none; so no fan-out-1 formula of size `opt` exists; so `tree > opt`. This
relies on a size-`opt` formula being a *model of the circuit-mode CNF*, which holds because such a
formula is necessarily dedup-free and dead-gate-free — either defect would prune it below `opt`,
contradicting the certified `opt`. Three independent reviewers (one per model family) checked this
step against the actual clauses and each confirmed it; it is the place to aim at first if you want
to break the result.
