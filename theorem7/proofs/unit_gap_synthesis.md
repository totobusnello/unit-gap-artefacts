# From refutation to theorem: the structure of gap=1 sharing in optimal AIGs

*A unified note on Theorem 7 of “The Unit Gap” (arXiv:2603.08033), tying together four results
(claims 0033–0036). Written for collaboration — every quantitative claim traces to a
DRAT-certificate or an exhaustive enumeration named in the “Artifacts” section.*

## Model

And-Inverter Graphs over `U₂`: 2-input AND gates, inversions free on every edge and on the
output, constant `1` free. `opt(f)` = minimum AND-gate count of a circuit (DAG) computing `f`;
`tree(f)` = minimum of a **formula** (every gate fan-out 1); `gap(f) = tree(f) − opt(f) ≥ 0`. A
**reconvergence** (“sharing”) is an internal gate with fan-out ≥ 2. This is the model of the
paper; our exact-synthesis encoder is cross-validated (G3) and every SAT model is re-checked by
simulation (`verify_circuit`).

Theorem 7 (Two-Mechanism), as stated:

> *In any size-optimal AIG with gap(f) = 1, the sharing arises from exactly one gate with
> fan-out 2, employing either dual-polarity or same-polarity reuse. No other sharing structure
> can produce gap = 1.*

The arc below: the statement is **false** (§1); no repair preserving its regularities survives
at n=4 (§2); the phenomenon that replaces it is a **certified, and now provably infinite,
family** (§3–§4).

---

## Contributions

Working inside Krinkin's AIG unit-gap framework, this note contributes:

1. **A certificate-backed refutation.** Machine-checked (drat-trim `s VERIFIED`) refutations of
   **Corollary 6** (the sharing term `s∈{0,1}`: we exhibit `s=3` for `⊕₃` and `s=6` for `⊕₄`)
   and **Theorem 7** (§1), plus an **exhaustive** n=4 census placing **72/222 NPN classes at
   gap≥2**. (Theorem 2's `gap≤1` bound is already contradicted by classical Schnorr + Khrapchenko
   bounds; our part there is to quantify it, not to refute it first. Note the census rests on the
   tree-DP + exact synthesis of claim 0026, *not* per-class DRAT — the drat-trim certificates back
   the Cor 6 / Thm 7 witnesses, `s=3`/`s=6`, and the flagship `0x03de`.)
2. **A complete structural characterization of the gap=1 stratum at n=4** (§1–§2): which classes
   force reconvergence, and the cardinality (up to 3) and degree (up to 3) of the sharing. The
   minimum-circuit enumeration itself is standard (cf. Berkeley IWLS'19); the
   *forced-reconvergence reading* is new.
3. **A forcedness certificate** (§2). A SAT/DRAT encoding that proves a structural invariant —
   *every* size-optimal AIG has ≥2 reconvergences — over the **entire** optimal set by a single
   UNSAT: encode “there exists an opt-gate circuit with ≤1 reconvergence” and certify it
   unsatisfiable. This certifies a property of *all* optima, not merely exhibits one witness. It
   is a natural instantiation of exact synthesis, but we did not find this certified-forcedness
   use in the literature.
   *Coverage of all optima (soundness of the certificate).* The encoding applies symmetry-breaking
   — operand ordering `a<b`, distinct operands `a≠b`, deduplication of identical gates, "no dead
   gate" (each gate feeds a later one), and a topological order with the output as the last gate.
   Every one of these is without loss of generality *at k = opt* — a dead, duplicate, or
   same-operand gate would yield a strictly smaller circuit, and reordering/relabelling is a
   renaming of the same DAG — and, crucially, **none changes any gate's fan-out**. So the
   canonicalization map from optimal AIGs to encoded models is fan-out-preserving: a size-optimal
   circuit with ≤1 reconvergence would map to a satisfying assignment with ≤1 reconvergence. The
   UNSAT therefore rules out *every* size-optimal circuit, not only canonical representatives.
4. **A closure / lift theorem** (§4). The forced-reconvergence family is *closed* under
   conjunction/disjunction with a fresh variable, with `opt` and `tree` each `+1` — yielding
   forced-reconvergence-type functions for **every n≥4** (the Lift Theorem). The lower bound is elementary
   (classical gate elimination); the contribution is the forced-multi *inheritance* and the
   resulting infinite family.

## §1 — Theorem 7 is false as stated (claim 0033, n=4)

The statement bundles three assertions; they must be separated.

- **Uniqueness / exhaustiveness** (“exactly one gate … no other sharing structure”): **false.**
- **The proof’s `s(a,b)=1` step** (via Corollary 6): **false** — Corollary 6 is itself refuted
  (claim 0025: `s` reaches 3 in ⊕₃, 6 in ⊕₄), and in the witnesses the top cut gives `s=3`.
- **Per-gate dual/same taxonomy:** *not* refuted (it is near-tautological: two consumers agree
  or disagree in polarity). We do not contest it.

Enumerating the size-optimal circuits of the **57 NPN classes with gap=1** at n=4:

- **37/57** admit an optimal AIG with **≥ 2 reconvergences** — contradicting “exactly one”.
- **6 are zero-conforming** (exhaustive): `0x0358, 0x0359, 0x03de, 0x06b5, 0x07bc, 0x178e` —
  **every** optimum has ≥ 2 reconvergences; no theorem-conforming optimum exists.

**Flagship witness `0x03de`** (opt=6, tree=7, gap=1), one optimal circuit:

```
g1 = x1 ∧ ¬x2      g4 = ¬g2 ∧ ¬g3        (g2, g3 have fan-out 2)
g2 = ¬x2 ∧ ¬x3     g5 = g2 ∧ g3
g3 = ¬x4 ∧ ¬g1     g6 = ¬g4 ∧ ¬g5        (output)
```

`g2`,`g3` reconverge; the two output-operand cones intersect in `{g1,g2,g3}`, so the top cut is
`s=3`, not 1. For `0x03de`, **`gap = 7 − 6 = 1` is DRAT-certified end-to-end** (opt: circuit
UNSAT k=1..5; tree: formula UNSAT k=1..6 + a 7-gate formula witness) and the circuit is
hand-checkable over the 16 rows. A second DRAT witness `0x0016` (opt=7) is in the artifacts.

## §2 — The structure of gap=1 sharing at n=4: forced, multiple, variable-degree (claim 0034)

One could hope to *rescue* Theorem 7 by weakening a constant. But its three regularities —
(i) cardinality “exactly one”, (ii) degree “fan-out 2”, (iii) exhaustiveness “no other
structure” — each fail **independently**:

- **(A) Cardinality is not 1.** `0x07bc` (opt=7): exhaustively, 48 optima, of which **24 have
  three** reconvergences and 24 have two — none has one.
- **(B) Degree is not universally 2.** `0x016e` (opt=8) has an optimum with a **single fan-out-3
  gate** (hand-checkable; gate 2 feeds gates 3,4,5). `opt(0x016e)=8` is DRAT-certified — the
  degree-3 optimum is provably size-optimal.
- **(Z) Uniqueness is impossible for six classes.** For the six zero-conforming classes,
  *“there exists an opt-gate AIG with ≤ 1 reconvergence”* is **UNSAT** (an at-most-one-shared
  SAT encoding), drat-trim `s VERIFIED`. Multiple reconvergence is **forced**.

So Theorem 7 does not merely lose a special case — three of its structural commitments each
break by a different mechanism. Degree-2 is not universal; single-reconvergence is impossible.

## §3 — Forced multiple reconvergence is not an n=4 artifact (claim 0035)

Call a function **forced-reconvergence-type** — the **forced-reconvergence family** , for the gap framework in
which it lives and the characterization given here; previously denoted `Z` — if it is gap=1 and
*every* size-optimal AIG has ≥ 2 reconvergences (forced multiple reconvergence). The six §2
classes are forced-reconvergence-type at n=4. The phenomenon persists at n=5, DRAT-certified end-to-end:

| function | | opt | tree | gap | forced-multi |
|---|---|---|---|---|---|
| `0x03de0000` | `0x03de ∧ x₄` | 7 | 8 | 1 | UNSAT (drat-trim `s VERIFIED`) |
| `0xffff03de` | `0x03de ∨ x₄` | 7 | 8 | 1 | UNSAT (drat-trim `s VERIFIED`) |

and once more at n=6: `0x3de000000000000` (`0x03de ∧ x₄ ∧ x₅`), opt=8, tree=9, gap=1,
forced-multi. Each leg — opt lower bound, tree/gap, forced-multi — is a separate DRAT proof.

## §4 — The Lift Theorem: forced-reconvergence-type functions exist for every n ≥ 4 (claim 0036)

The n=4→5→6 witnesses are all of the form `z ∧ x_new` / `z ∨ x_new`. This is a lemma:

> **Lift lemma.** If `z` is forced-reconvergence-type (forced-multi, gap=1) on n variables, then `z ∧ x_{n+1}` and
> `z ∨ x_{n+1}` are forced-reconvergence-type on n+1 variables, with `opt` and `tree` each `+1` (gap preserved).

**Proof (full, self-contained, `proof_lift_lemma.md`).** *Upper bound:* an optimal `z`-circuit
plus one AND with `x` gives `opt(z∧x) ≤ opt(z)+1`. *Lower bound:* restrict `x=1` (so `z∧x` ↦ `z`);
since `z ≢ 0,1`, at least one gate reads `x` and, under the restriction, becomes a pass-through
or constant and is spliced out (in an optimal lift, exactly one, and positively) — constant-
propagation then yields a `z`-circuit with one fewer
gate, so `opt(z∧x)=opt(z)+1`. *Forced-multi inheritance:* in an optimal lift the restriction
eliminates exactly one gate, and contracting that single pass-through is non-increasing in the
reconvergence count (a four-case fan-out analysis), so the resulting optimal `z`-circuit would
inherit ≤ 1 reconvergence — impossible, as `z` is forced-reconvergence-type. *Formulas* (tree) are handled directly
by pruning a minimum formula (with dead-code removal), and the `∨` case is the `x=0` dual.

> **Lift Theorem.** For every `n ≥ 4` there is an `n`-variable Boolean function that is gap=1
> with forced multiple reconvergence — i.e. the forced-reconvergence family is non-empty at every `n ≥ 4`.

*Proof.* Take the n=4 flagship `z₄ = 0x03de` (forced-reconvergence-type, DRAT-certified) and set
`z_{n+1} := z_n ∧ x_{n+1}`; the lemma makes each `z_n` forced-reconvergence-type. ∎

**Corroboration** (independent of the proof): n=3-exhaustive check of `opt(z∘x)=opt(z)+1` (all
218 essential functions, 0 violations); the DRAT chain n=4→5→6; a forced-multi-inheritance probe
(0 losses over the six n=4 forced-reconvergence classes).

---

## What this establishes

Theorem 7 aimed to say gap=1 sharing is a *single, degree-2* event. The truth at n=4 is the
opposite for a robust family: reconvergence is **multiple and forced**, of variable cardinality,
and not confined to degree 2 — and by §4 this is a genuine phenomenon at **every** `n ≥ 4`, not
a small-case artifact. The program that began as a refutation of Theorem 7 ends with a positive
structural theorem about optimal AIGs.

## Related work and novelty

The gap between formula size and circuit size is classical, but the classical literature (Wegener,
*The Complexity of Boolean Functions*; Jukna, *Boolean Function Complexity*) studies it over
**general bases**, where it can be superpolynomial. The **AIG unit-gap regime** — `gap ∈ {0,1}`
with free inversions — is the framework of Krinkin (arXiv:2603.08033); we work inside it.

Our §1–§2 enumeration uses standard **exact synthesis** (SAT-based minimum-circuit search per NPN
class), the methodology of e.g. Soeken–Haaswijk–De Micheli and the Berkeley IWLS'19 note
*Enumeration of Minimum Fanout-Free Circuit Structures* (which counts minimum structures per NPN
class up to 5 inputs). What is new here is not the enumeration but its **structural reading**:
that gap=1 *forces* multiple reconvergence (§2, the opposite of Krinkin's Theorem 7). The lift
lower bound (§4) uses the classical **gate-elimination / restriction** method (Schnorr); we do not
claim its arithmetic `opt(f∧x)=opt(f)+1` as deep — the contribution is the **forced-multi
inheritance** and the resulting **all-n family**.

The **forcedness certificate** (§2, contribution 3) needs careful positioning. The logical
method — encode "an opt-gate circuit with ≤1 reconvergence exists" and certify UNSAT — is
*standard*: it is the dual of **backbone** testing (a literal true in all models is checked by
adding its negation and testing UNSAT) and a special case of counterexample elimination. Its
ingredients all exist: exact-size SAT encodings (Haaswijk–Soeken–Mishchenko–De Micheli),
all-optima enumeration by blocking clauses (Fišer–Háleček–Schmidt 2017; Lee–Jiang–Mishchenko–
Brayton, IWLS'19), and certified optimization / proof logging (VeriPB, Bogaerts et al.). What we
did *not* find is any prior paper that uses a **DRAT-certified counterexample encoding to prove a
nontrivial *structural* invariant shared by every size-optimal circuit** (as opposed to proving
the optimum *value*, exhibiting one optimum, or enumerating optima). We therefore claim it only
as a natural, previously-underused instantiation — not a new technique. The **lift** (contribution
4) sits
beside work on how optimal size behaves under extending a function by structure — e.g. Ilango's
`f`-Simple Extension Problem and *Simple Circuit Extensions for XOR* (arXiv:2511.16903) — though
those study extension complexity, not a closure operation preserving forced reconvergence.

To our knowledge no prior work states forced multiple reconvergence at gap=1, nor an
all-`n` forced-reconvergence family; a targeted sweep of exact-synthesis venues and the standard
complexity texts returned only Krinkin's paper on these exact terms. (A full check against
textbook folklore is still advisable before journal submission.)

## Honest scope

- **Density: there is a seventh class — the family is not lift-generated (resolved).** Write
  `F_n` for the number of NPN classes of `n`-variable forced-multi gap=1 functions. Then
  `F₄ = 6` (exhaustive, machine-verified: the six classes of §2), `F₅ ≥ 6` from the AND-lifts,
  and — settling the density question — **`F₅ ≥ 7`: there exist non-canalizing (non-lift)
  forced-multi gap=1 functions at n=5.** Three explicit witnesses which an exhaustive
  canonicalization over the full NPN group of `n=5` (all `5!·2⁵·2 = 7680` transforms) certifies to
  be three *distinct* classes, each also distinct from all six lifts, so `F₅ ≥ 9`:

  > `f = 0x03de ∧ (¬x₀ ∨ x₄)` (`0x03de0154`), `0x03de ∨ (x₀ ∧ x₄)` (`0xabfe03de`),
  > `0x03de ∨ (¬x₀ ∧ x₄)` (`0x57df03de`) — each **5-essential, non-canalizing, opt=8, tree=9,
  > gap=1, forced-multi**.

  So conjecture **B′** (*every forced-multi gap=1 function is canalizing*, i.e. `F₅ = 6`) is
  **false**: the forced-reconvergence family is genuinely richer than the lift tower. Each witness is
  machine-verified — `opt=8` (k=1..7 circuit-UNSAT DRAT + a `verify_circuit`'d k=8 model,
  symmetry-break-independent); `gap=1` (a `verify_circuit`'d fan-out-1 formula at k=9 gives
  `tree ≤ 9`, and forced-multi gives `tree ≥ 9`, self-certifying); and forced-multi (the
  at-most-one-shared encoding is UNSAT at k=opt, drat-trim-verified). For the witness the
  forced-multi UNSAT is obtained **without any symmetry break** — the vetted encoder plus an
  UNSAT-targeted solver closes k=8 directly (66 s), so the certificate is a plain DRAT with no
  reliance on a symmetry-breaking soundness argument. (A gate-ordering symmetry break, proven
  WLOG by three independent analyses, is used only to *accelerate* the harder opt=9 instances and
  the sweep; it is off the witness's trusted path.)
  - *Construction (the shape that works).* The witnesses are `z ∧ (ℓ ∨ x₄)` — the lifting
    literal absorbed into an *existing* variable, so the independence gadget sits **beside** `z`
    rather than substituted **into** its inputs. This keeps `opt = opt(z)+2` and `tree = opt+1`,
    avoiding the formula-duplication that pushed the naive parity graft `0x03de(x₀⊕x₄,…)` to
    `gap ≥ 2` (that candidate is forced-multi but *not* gap 1, hence not a witness).
  - *Why the earlier heuristics pointed the other way.* A sampled census had found only
    non-forced-multi non-canalizing gap=1 functions, and every *substituted* construction paid a
    gap penalty — the "cost of independence" is real but not fatal: absorbing the literal beside
    `z`, at one specific literal polarity, keeps the gap at 1 while breaking canalization.
- **The theorem is a paper proof** in the AIG model (reviewed, and with DRAT-certified base and
  n=4/5/6 instances); it is not yet machine-checked (Lean). A formalization would be a separate
  effort.
- **Encoder→CNF** is a semantic bridge outside DRAT, mitigated by G3 cross-validation and
  per-circuit `verify_circuit`.
- **Scope** is specific DRAT witnesses at n=5/6 plus the general lemma; n ≥ 5 exhaustive
  enumeration is infeasible (616k+ NPN classes).

## Artifacts (paths as in the private tree)

- Per-claim technotes: `notes/technote_thm7_refutation.md` (0033),
  `notes/technote_thm7_substitution.md` (0034), `notes/technote_z_generalization.md` (0035),
  `notes/proof_lift_lemma.md` (0036, the full proof).
- Code: `experiments/exp_krinkin_cor6/` — `thm7_check.py`, `zc_certify.py` (at-most-one-shared),
  `n5_forced_test.py`, `n5_directed.py`, `lift_lemma_empirical_test.py`; encoder
  `experiments/exp_gate_0001/aig_exact.py`.
- DRAT certificates: `experiments/exp_krinkin_cor6/certs/` (e.g. `zc_0x03de_amo1shared.drat`,
  `opt_0x016e_k7.drat`, `n5_0x03de0000_amo1shared.drat`) — each verified with `drat-trim`
  (`s VERIFIED`); SHA-256 prefixes recorded in the accompanying `*_witness.json` / ledger.
