# Technote — The forced-multiple-reconvergence family (Z) generalizes beyond n=4

> **Claim `7P-PNP-CLM-0035`** (FINITE_SCOPE_VERIFIED, n=5 witnesses, 2026-08-07). Succeeds
> claim 0034. Where 0034 established the family Z at n=4 (gap=1 AIGs whose *every* size-optimal
> realization has ≥2 fan-out-2 gates — forced multiple reconvergence), this note shows the
> phenomenon is **not an artifact of n=4**: it persists at n=5, DRAT-certified, and a **proved**
> lift lemma (`proof_lift_lemma.md`) extends it to all n≥4 (claim 0036). LASTRO standard
> (`../13_WRITEUP_STANDARD.md`).
>
> **Naming:** the family denoted `Z` throughout this note is the **forced-reconvergence family** 
> — see `unit_gap_synthesis.md` and the **Lift Theorem** (0036). `Z` is kept here only as
> the historical shorthand.

## Context

Claim 0034 (`technote_thm7_substitution.md`): at n=4 there are exactly six NPN classes whose
every size-optimal AIG has ≥2 reconvergences — *"there is an opt-gate AIG with ≤1 fan-out-≥2
gate"* is UNSAT (DRAT). Open question it left: is this Z phenomenon specific to n=4, or does it
generalize? AIG basis = 2-input AND gates, free edge/output inversions; `opt`/`tree` = min
circuit/formula gate count; `gap = tree − opt`; "reconvergence" = fan-out ≥ 2.

## Result — Z witnesses at n=5 (DRAT-certified)

Two 5-variable functions are gap=1 with **forced** multiple reconvergence, certified end-to-end:

| function | | opt | tree | gap | forced-multi (at-most-one-shared UNSAT) |
|---|---|---|---|---|---|
| `0x03de0000` | `0x03de ∧ x4` | 7 | 8 | 1 | UNSAT, drat-trim `s VERIFIED`, `drat_sha=8bcaac62…` |
| `0xffff03de` | `0x03de ∨ x4` | 7 | 8 | 1 | UNSAT, drat-trim `s VERIFIED`, `drat_sha=d712ca37…` |

For each: `opt` DRAT lower bound (circuit UNSAT k=1..6), `opt` witness at k=7 (`verify_circuit`),
`tree` DRAT (formula UNSAT k=7 + formula witness k=8 ⟹ tree=8, **gap=1 DRAT end-to-end**), and
the at-most-one-shared UNSAT (⟹ no size-optimal AIG has ≤1 reconvergence ⟹ forced-multi).
Both derive from the n=4 flagship `0x03de` (claim 0033/0034) via a single-variable gate. Artifacts:
`n5_forced_test.py`, `certs/n5_*`; found by directed construction (`n5_directed.py`) over the
six n=4 Z classes (among the *decided* candidates, 2 were gap=1 and both were forced-multi; the
screener silently drops timeouts/inconclusive, so this is not a count over all 72 essential).

## The lift lemma (toward all n≥4)

The two witnesses are `z ∧ x_new` and `z ∨ x_new` of a Z function `z`, both preserving
(forced-multi, gap=1) with opt and tree each +1. This suggests:

> **Lift lemma (proved — full proof in `proof_lift_lemma.md`).** If `z` is forced-multi with
> gap=1 on n variables, then `z ∧ x_{n+1}` (and `z ∨ x_{n+1}`) is forced-multi with gap=1 on n+1
> variables, with `opt(z∧x)=opt(z)+1`, `tree(z∧x)=tree(z)+1`, gap preserved.

*Argument (full proof in `proof_lift_lemma.md`).* **Upper bound:** an
optimal `z`-circuit followed by one AND with `x_{n+1}` gives `opt(z∧x) ≤ opt(z)+1`. **Lower
bound:** take any `m`-gate circuit `C` for `z∧x` and restrict `x_{n+1}=1`. Since `z∧x` depends on
`x_{n+1}`, some gate of `C` reads it directly; under the restriction that gate collapses to a
constant or to a literal of its other input and is eliminable (composing the free inversions).
Constant-propagation yields an AIG for `z` with at most `m−1` gates, so `m−1 ≥ opt(z)`, i.e.
`m ≥ opt(z)+1`. Hence `opt(z∧x)=opt(z)+1` — no shared use of `x_{n+1}` can beat it. The same
restriction argument on formulas preserves fan-out 1, giving `tree(z∧x)=tree(z)+1`; gap stays 1.
The `∨` case follows by duality and free inversions. **Forced-multi inheritance:** in an optimal
lift (`opt(z)+1` gates) the restriction eliminates *exactly one* gate (it cannot drop below
`opt(z)`); the shared-gate count does not decrease under that single contraction (a consumer of
both the eliminated gate `g` and its collapse-target `h` would force a second simplification,
contradicting the single elimination), so ≥2 reconvergences persist. *(The earlier phrasing "any
circuit contains an optimal z-circuit" was literally false — a lift may mix `x_{n+1}` throughout;
the z-circuit is the one obtained **by restriction and simplification**.)*

**Empirical check n=5 → n=6:** lifting the n=5 witness once more, `0x03de ∧ x4 ∧ x5` at n=6
(`0x3de000000000000`): **CONFIRMED** — opt=8, tree=9, gap=1, forced-multi, all DRAT-certified
(drat-trim `s VERIFIED`; `drat_sha=0bdb5b96…`). So the lift preserves (forced-multi, gap=1)
with opt+1/tree+1 across n=4→n=5→n=6, exactly as the lemma predicts.

**Consequence — now a theorem (the lemma is proved).** The lift lemma has a full, self-contained
proof in `proof_lift_lemma.md`. Iterating the lift from the n=4 flagship therefore yields
forced-multi gap=1 (Z-type) functions for **every n≥4**, unconditionally — the Z phenomenon is
genuinely infinite, not an artifact of n=4.

## Ledger (lastro) and honest caveats

- **DRAT (strong):** the two n=5 witnesses, all three legs each (opt LB, tree gap=1,
  forced-multi), drat-trim `s VERIFIED`, SHAs in `certs/`.
- **Existence, not density:** both n=5 witnesses are lifts of the *same* n=4 flagship `0x03de`
  — this is an existence result, not a claim about how common forced-multi is at n=5, nor a
  structural characterization. Structurally-independent n=5 witnesses (from the sampled AIG
  census `aig_n5_census.py`) are a separate, ongoing line.
- **Lemma is proved:** the lift lemma now has a full, self-contained proof
  (`proof_lift_lemma.md`), corroborated by n=3-exhaustive (opt+1, 0 violations) and the
  DRAT-certified n=4→n=5→n=6 chain. "All n≥4" is therefore unconditional (claim 0036).
- **encoder→CNF link:** non-DRAT semantic bridge, mitigated by G3 + `verify_circuit` (same caveat
  as claims 0024/0031/0033/0034).
- **Scope:** specific DRAT-certified witnesses at n=5 (and n=6 for the lift check); n=5+ exhaustive
  is infeasible (616k+ NPN classes). Succeeds claim 0034 (`technote_thm7_substitution.md`).
