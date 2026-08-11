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
  n = 5 has **at least fifteen** — **eleven** lift classes plus **four non-lifts** — all checked
  pairwise distinct by exhaustive canonicalisation over the full NPN group, in pure Python with no
  solver. So the family is a genuine object, not one small case propagated by a construction.
  *Corrected 2026-08-11:* this said "at least ten" because the counting script generated only the
  AND-lifts while the Lift Theorem covers `z ∧ x` **and** `z ∨ x`. Counting both directions the lift
  closure is 11 classes, not 6 — 6 + 6 with exactly one collision, at the single NP-self-complementary
  class among the six. Found by Kirill Krinkin, reading the artefacts without a solver.
- **The count splits by trust path, and this file states the split rather than averaging it.** Two of
  the four non-lifts — `0x03de0154` and `0x09c50800` — have their forced-multi certificate produced
  **with no symmetry breaking at all** (vetted encoder, `gate_order_b = False`), and those are the two
  whose CNF hashes are pinned in `verify/manifest.csv`. The other two (`0xabfe03de`,
  `0x57df03de`) were certified **through the `gate_order_b` WLOG-ordering**, so no no-SB CNF exists to
  pin for them. Therefore:
  - **`F₅ ≥ 13` needs no symmetry-breaking argument** — the eleven lift classes (by the Lift Theorem,
    from the no-SB-certified n = 4 base) plus those two pinned non-lifts;
  - **`F₅ ≥ 15`** additionally rests on the soundness of that ordering, which is a lemma proved by
    three independent analyses — not a certificate.

  **What this does not weaken:** the conjecture that the family is only its lift closure needs just
  **one** non-canalizing forced-multi gap-1 function to fall, and `0x03de0154` is one whose forcedness
  is pinned without any ordering argument. The headline — *the family exceeds its own closure* — sits
  entirely on the no-SB path. The ordering-dependent pair raises the count from 13 to 15 and carries no
  other weight. An earlier version of this file said "at least ten" without the split; the correction
  is dated 2026-08-11 and came from an adversarial audit (Codex REV-0107).

One of the four non-lifts, **`0x09c50800`**, is the interesting one: every other witness came from a
directed sweep on one family, while this one fell out of a random census. Existence-by-construction and
existence-by-accident are evidence of different kinds. See *A class nobody aimed at* below.

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

### What ships as a proof, and what you must regenerate — updated 2026-08-11

The bundle now carries the **complete `opt` chain of the flagship witness `0x03de0154`**: CNF **and**
DRAT for every `k = 1..7`, about 35 MB, of which the `k = 7` proof alone is 27.9 MB. That is a
deliberate exception to this file's own "reproducibility, not blobs" principle, declared and dated in
`tools/blob_exceptions.txt`, and it is the only one.

The reason: `opt ≥ 8` **is** the UNSAT at `k = 7`. Without that proof shipped, the refutation of the
lift-closure conjecture is not checkable by a reader who has `drat-trim` but declines to run a SAT
solver — a legitimate reviewer stance, and exactly where Kirill Krinkin stopped when he checked these
artefacts without a solver on 2026-08-11. Every leg was verified on **two machines with independently
built `drat-trim`** (a Linux VPS and a Mac): `s VERIFIED` on both.

So, with `drat-trim` alone and no solver at all:

```sh
cd verify/sample_certs
for k in 1 2 3 4 5 6 7; do drat-trim n5_0x03de0154_opt_k$k.cnf n5_0x03de0154_opt_k$k.drat; done
```

Seven `s VERIFIED` lines give `opt(0x03de0154) ≥ 8`; with the `k = 8` model — a circuit, re-simulated
rather than solved — that closes `opt = 8`.

**What still needs one solver run, and it is one.** The forced-multi certificate: its DRAT runs to
hundreds of megabytes (the sibling witness's is 379 MiB), so it cannot ship and its CNF hash is pinned
instead (`ed3b8350f72f8078`). It regenerates in about 66 s with `kissat --unsat`. That same UNSAT is
what gives `tree ≥ 9`, hence `tree = 9`. Stating the cost beats leaving a gap for the reader to find.

The second no-symmetry-breaking witness, `0x09c50800`, ships at `k ≤ 4` and regenerates the rest. Its
value is **provenance** — it fell out of a random census rather than a directed sweep — and its chain
has the same shape as the flagship's, so duplicating 30 MB would add bytes, not evidence.

The script prints the SHA of each regenerated CNF; compare against `verify/manifest.csv`
(claim → leg → CNF SHA → verdict). The forced-multi leg's CNF SHA is pinned there
(`ed3b8350f72f8078`) and regenerates byte-identically on any machine.

**Zero-setup spot check** (only `drat-trim` needed). Committed certificates live in
`verify/sample_certs/`: the **full** opt chain `k = 1..7` for the flagship (see above), and
`k ≤ 4` for the other witnesses. One leg, to see the shape:

```sh
drat-trim verify/sample_certs/n5_0x03de0154_opt_k3.cnf \
          verify/sample_certs/n5_0x03de0154_opt_k3.drat   # expect: s VERIFIED
```

## Count the classes (F₅ ≥ 15)

```sh
python3 experiments/npn_check_f5.py [private tree]
```

Pure Python, no solver, seconds to run: canonicalizes every witness over the full n = 5 NPN group (all
7680 transforms) and reports **15** distinct classes — **11** in the lift closure (6 AND-lifts + 6
OR-lifts, exactly one collision) plus the 4 non-lifts. It also asserts *why* there is exactly one
collision: `OR-lift(z) ≅ AND-lift(¬z)` under NPN spends the output negation, so the two lifts of `z`
coincide iff `z` is NP-self-complementary, and exactly one of the six n = 4 classes is. The check fails
loudly if that explanation ever stops holding.

The older `npn_check_f5.py` is superseded: it lifted only by AND and therefore reported 10.

This script establishes **distinctness**, which is solver-free and therefore the cheapest part to
trust. It does **not** establish that each of the ten is forced-multi; that comes per witness from the
certificates, and two of the four non-lifts get theirs through the `gate_order_b` WLOG-ordering rather
than the no-SB path — see *What is claimed* above, and `manifest.csv`, which pins CNF hashes only for
the two no-SB witnesses. A reader who accepts only plain DRAT gets `F₅ ≥ 13`; the ordering lemma takes
it to 15.

## A class nobody aimed at

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
evidence of different kinds, and the family having both is what this witness contributes. The
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
