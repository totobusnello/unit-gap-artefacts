# VERIFY — reproduce and machine-check the results

A self-contained guide to independently verify the core unit-gap / forced-reconvergence results.
It relies only on public tools and this repo.

**What this repository reproduces from scratch** (no trust required): the seventh, non-lift n=5
witness `0x03de0154` end-to-end (opt, tree, forced-multi), the two other non-lift n=5 witnesses and
the n=4 Lift base by the same one script, and the exhaustive NPN class count. **What it does not
re-run here** (established in the full development, not this curated tree): the n=4 gap census
(the "72/222 gap≥2" / "exactly six forced-multi classes" statements), the n=6 corroboration, and the
n=3 exhaustive lift sweep, and an auxiliary n=4 witness (`0x0016`) — those are cited, not reproduced here.

**Principle: reproducibility, not blobs.** Some DRAT proofs are hundreds of MB, so we do not ship
them. We ship the encoder, a one-command regenerator, and the pinned **CNF SHA** of each instance.
A CNF's hash is deterministic from the encoder (machine-independent). A DRAT's bytes are **not**
deterministic across solver builds/versions — so the portable acceptance test is "`drat-trim`
reports **VERIFIED** on the regenerated CNF", not equality of DRAT bytes. (The `cnf_sha16` values in
`verify/manifest.csv` are the first 64 bits of SHA-256; for a stronger check recompute the full
SHA-256 yourself. Pin your `kissat`/`drat-trim` build if you want bit-for-bit CNF stability.)

## What is claimed (honest scope)

- Krinkin's Theorem 7 (a unit gap comes from *exactly one* shared gate) is **false**; the opposite
  holds and is *forced*: some functions have **every** size-optimal AIG carrying ≥ 2 reconvergent
  (fan-out ≥ 2) gates. At n = 4 there are exactly six such NPN classes — the *exhaustiveness*
  (exactly six) is from the census in the full development, while each of the six classes' own
  opt/tree/forced-multi is reproducible here via `reproduce_witness.py <tt> <opt>`.
- **Closure / Lift Theorem** (`proofs/proof_lift_lemma.md`): if `z` is forced-multi with gap = 1,
  so are `z ∧ x_new` and `z ∨ x_new` — hence the family exists for every n ≥ 4. Its n=4 base
  (`0x03de`) is reproducible here; n=5, n=6 instances corroborate.
- **Additional non-lift classes at n = 5.** There is a seventh, non-lift class — witness
  `f = 0x03de ∧ (¬x₀ ∨ x₄)` (`0x03de0154`): non-canalizing, opt = 8, tree = 9 (gap = 1),
  forced-multi. Counting NPN classes, n = 5 has **at least nine** (three non-lifts + six lifts),
  verified by exhaustive canonicalization over the full NPN group. (This is a class-count lower
  bound, not a density/proportion.)

This is a structural result in exact circuit synthesis — **not an asymptotic or lower-bound
result.** The narrative with references and honest caveats is in `proofs/unit_gap_synthesis.md`.

**Target of the refutation.** Theorem 7 as stated in arXiv:2603.08033 (v1/v2). The paper was
**withdrawn on 2026-08-04** (its Theorem 2 is false); the withdrawal notice states Theorem 7 lost
its proof. This repository establishes the stronger fact that Theorem 7's *statement* is false and
the opposite is forced. See the [current arXiv record](https://arxiv.org/abs/2603.08033).

## Setup (a few minutes)

Two binaries on your `PATH`: `kissat` (SAT solver + DRAT) and `drat-trim` (DRAT checker).

```sh
git clone https://github.com/arminbiere/kissat   && ( cd kissat   && ./configure && make )   # -> build/kissat
git clone https://github.com/marijnheule/drat-trim && ( cd drat-trim && make )                # -> drat-trim
# put both on PATH
```

Only `python3` (≥ 3.8), `kissat`, and `drat-trim` are needed.

## Reproduce the witnesses

```sh
python3 verify/reproduce_witness.py                 # 0x03de0154 (default n=5): opt LB (k=1..7 UNSAT,
                                                    #   drat-trim VERIFIED), opt & tree SAT witnesses
                                                    #   (verify_circuit self-certifying), canalizing report
python3 verify/reproduce_witness.py 0xabfe03de 8     # 2nd non-lift n=5 witness
python3 verify/reproduce_witness.py 0x57df03de 8     # 3rd non-lift n=5 witness
python3 verify/reproduce_witness.py 0x03de 6         # the n=4 base of the Lift Theorem
python3 verify/reproduce_witness.py 0x03de0154 8 --full   # also the forced-multi certificate
                                                    #   (large DRAT, ~minutes; no gate-ordering SB)
```

The script prints the SHA of each regenerated CNF; compare against `verify/manifest.csv`. The
default witness's forced-multi CNF SHA is pinned (`ed3b8350f72f8078`).

**Zero-setup spot check** (only `drat-trim` needed): committed sample certificates for the opt
lower bound, k = 1..4, live in `verify/sample_certs/` (read-only; `reproduce_witness.py` writes its
regenerated artifacts to `verify/_generated/`, not here):

```sh
drat-trim verify/sample_certs/n5_0x03de0154_opt_k3.cnf \
          verify/sample_certs/n5_0x03de0154_opt_k3.drat     # expect: s VERIFIED
```

## Count the classes (≥ 9 at n = 5)

```sh
python3 verify/npn_check_bk5.py
```

Pure Python, no solver: canonicalizes the three non-lift witnesses and the six lifts over the full
n = 5 NPN group (all 7680 transforms) and confirms nine distinct classes. (It checks distinctness
and non-canalizing status; each witness's forced-multi/gap=1 is reproduced by `reproduce_witness.py`.)

## Layout

- `proofs/` — `proof_lift_lemma.md` (the Lift Theorem, full proof) and `unit_gap_synthesis.md`
  (the full synthesis: Theorem 7 refutation → positive structure → non-lift classes, with honest scope).
- `encoder/` — `aig_exact.py` (the AIG exact-synthesis SAT encoder + an independent `verify_circuit`
  that simulates a decoded circuit against the full truth table, making every SAT witness
  self-certifying), `n5_forced_test.py` (`build_amo_shared`, the at-most-one-shared forced-
  reconvergence encoding), `zc_certify.py` (CNF/DRAT helpers).
- `verify/` — `reproduce_witness.py`, `npn_check_bk5.py`, `manifest.csv`, `sample_certs/`.

## Trust boundary

The forced-multi certificate adds **no gate-ordering symmetry break**. It does use the base
encoder's structural normalizations — operand order `a<b`, no duplicate gate, no dead gate,
output-last — each of which is without loss of generality *at a proven optimum* (a violating
circuit would not be size-optimal) and, crucially, fan-out-preserving; so the UNSAT rules out
*every* size-optimal circuit, not just canonical ones. (A gate-*ordering* WLOG constraint exists in
the code only to speed up harder instances; it is off this trusted path, and its machine-certified
dominance version is future work.) Each SAT witness is confirmed by `verify_circuit` independently
of the SAT solver, so the encoder→CNF translation is checked semantically, not assumed.
