# The Lift Lemma — a full proof

> Companion to `technote_z_generalization.md` (claim `7P-PNP-CLM-0035`). This note
> upgrades the *sketch* of the lift lemma to a complete proof, and derives the
> unconditional consequence: **forced-multiple-reconvergence gap=1 (forced-reconvergence family) functions
> exist for every n ≥ 4.** LASTRO standard (`../13_WRITEUP_STANDARD.md`).

## Model and definitions

We work in the And-Inverter Graph (AIG) model over the basis U₂ used throughout this
repository (`aig_exact.py`, validated cross-check G3):

- A **circuit** is a DAG. Sources are the input variables `x₁,…,x_n` and the constant `1`.
  Every internal node is a **2-input AND gate**. Every edge and the output may be freely
  inverted (inversions are free — they cost nothing).
- `opt(f)` = minimum number of AND gates in a circuit computing `f`.
- A **formula** (tree) is a circuit in which every *gate* has fan-out exactly 1 (input
  variables may be reused). `tree(f)` = minimum number of AND gates in a formula for `f`.
- `gap(f) = tree(f) − opt(f) ≥ 0`.
- A **reconvergence** is an internal AND gate with fan-out ≥ 2. (Inputs do not count — this
  matches the at-most-one-shared encoding in `zc_certify.py`, whose sharing variables range
  over gate nodes `n+1,…,n+k` only.)
- `f` is **forced-multi** if *every* size-optimal circuit for `f` (i.e. with exactly `opt(f)`
  gates) has ≥ 2 reconvergences. Equivalently: "there is an `opt(f)`-gate circuit with ≤ 1
  reconvergence" is unsatisfiable.

Throughout, `z` is a Boolean function of `x₁,…,x_n` with `z ≢ 0` and `z ≢ 1`, and we write
`x := x_{n+1}` for a fresh variable. `f := z ∧ x`.

---

## Lemma (Lift Lemma)

> If `z` is forced-multi with `gap(z) = 1` on `n` variables, then `f = z ∧ x_{n+1}` is
> forced-multi with `gap(f) = 1` on `n+1` variables, and
> `opt(f) = opt(z) + 1`, `tree(f) = tree(z) + 1`.
> The same holds for `z ∨ x_{n+1}`.

We prove the `∧` case in full; the `∨` case is identical after one sign change (§7).

---

## 1. Upper bound: `opt(f) ≤ opt(z) + 1`

Take an optimal circuit for `z` (`opt(z)` gates) and add one AND gate whose inputs are the
output wire of `z` and the variable `x`. Its output is `f = z ∧ x`. This uses `opt(z)+1`
gates. ∎

## 2. The restriction and constant propagation

Let `C` be **any** circuit for `f` with `m` gates. Apply the restriction `σ : x = 1`.
`f|σ = z ∧ 1 = z`, so `C|σ` computes `z`.

Constant-propagate `C|σ`: an AND gate with a constant-`1` input becomes a pass-through to
its other input (possibly inverted); an AND gate with a constant-`0` input becomes the
constant `0`; inversions of constants are constants. A pass-through gate is spliced out — its
consumers read its surviving input directly, composing the free inversions — and a constant
gate is likewise spliced out. Simplification **never creates a gate**; it only removes gates
and rewires. Let `C'` be the result: a circuit for `z` with `m' ≤ m` gates.

## 3. Lower bound: `opt(f) = opt(z) + 1`

Because `z ≢ 0`, `f = z ∧ x` depends on `x`; hence `x` enters `C`. It cannot enter only as the
output wire (that would force `f ∈ {x, ¬x}`, impossible since `z ≢ 0,1`), so at least one gate
of `C` takes `x` (possibly inverted) as a direct input. Fix such a gate `g`.

Under `σ` the `x`-input of `g` becomes the constant `1` (if `g` reads `x` positively) or `0`
(if it reads `¬x`). Either way `g` becomes a pass-through or a constant, i.e. `g` is spliced
out. So **at least one gate is removed**: `m' ≤ m − 1`. Since `C'` computes `z`,
`opt(z) ≤ m' ≤ m − 1`, i.e. `m ≥ opt(z) + 1`.

Taking `C` optimal gives `opt(f) ≥ opt(z)+1`; with §1, `opt(f) = opt(z) + 1`. ∎

## 4. Structure forced by optimality

Now let `C` be an **optimal** circuit for `f`, so `m = opt(f) = opt(z)+1`. From §2–3,
`opt(z) ≤ m' ≤ m−1 = opt(z)`, hence `m' = opt(z) = m − 1`: **exactly one gate is eliminated**
by the restriction-and-simplify. Two structural facts follow.

**(a) Exactly one gate reads `x`; it has one positive `x`-input and one non-`x` input `a`, and
`g|σ = a` (a pass-through).**
If two or more gates read `x`, each is spliced under `σ`, giving `m' ≤ m−2`, contradicting
`m' = m−1`. So exactly one gate `g` reads `x`. Enumerate `g`'s two inputs.

- *Both inputs are `x`-literals.* Then `g|σ` is a **constant**: `AND(x,x)=x → 1`,
  `AND(x,¬x)=0`, `AND(¬x,¬x)=¬x → 0` under `x=1`.
- *One input is a non-`x` wire `a`, the other reads `¬x`.* Then `g|σ = AND(a, 0) = 0`, again a
  **constant**.
- *One input is a wire `a` (not an `x`-literal), the other reads `x` positively.* Then
  `g|σ = AND(a,1) = a`, a **pass-through**. (If `a` is itself the constant `1`, `g|σ = 1` is
  constant and falls under the constant case above — such a gate never occurs in an optimal
  circuit anyway.)

In the two constant cases `g|σ` is a constant `κ`. `g` cannot be the sole output (that would
make `f|σ = z` constant, contradicting `z ≢ 0,1`), so `g` feeds some gate `c = AND(g^{π}, d)`;
under `σ`, `c = AND(κ^{π}, d)` is either the constant `0` (collapses) or `AND(1,d)=d` (a
pass-through) — either way `c` is eliminated too. That is a **second** elimination, contradicting
`m' = m−1`. Hence both constant cases are impossible: `g` has exactly one input reading `x`
**positively** and one non-`x` input `a`, and `g|σ = a`.

**(b) No cascade.** The single elimination is `g` itself; `a` and every other gate survive
in `C'` (else `m' < opt(z)`, impossible).

## 5. `tree(f) = tree(z) + 1` and gap

The upper bound `tree(f) ≤ tree(z)+1` is §1 with a formula for `z` (adding one AND leaf `x`
keeps fan-out 1). For the lower bound we argue directly on formulas — *not* via §4, because a
tree-optimal formula need not be a size-optimal circuit, so §4's optimality-driven
"exactly-one-elimination" does not apply here. Take **any** minimum formula `F` for `f`
(`tree(f)` gates). Restrict `x=1` and prune constants and pass-throughs as in §2. Two facts:
(i) at least one gate is removed — by §3, `f` depends on `x`, so `F` has a gate reading `x`,
and it becomes a constant or pass-through under `σ`; (ii) after also **garbage-collecting dead
gates**, the result is again a formula. Pruning a pass-through splices its *unique* consumer
onto its input; pruning a constant removes it and can leave its other input subtree **dead**
(fan-out 0) — e.g. `g = AND(¬x, a) → 0` under `σ` orphans the subtree feeding `a`. Delete every
such dead gate: this is function-preserving and only lowers the count, and it restores fan-out
exactly 1 for the survivors (each surviving non-root gate keeps a single consumer — splicing a
pass-through merely redirects its edge onward, so the consumer chain terminates at a surviving
gate or at the output root). Hence the
pruned, garbage-collected `F'` is a **formula** for `z` with at most `tree(f) − 1` gates, so
`tree(z) ≤ tree(f) − 1`. With the upper bound, `tree(f) = tree(z) + 1`. (The `∨` analog in §7
inherits the same dead-code step.)

Therefore `gap(f) = tree(f) − opt(f) = (tree(z)+1) − (opt(z)+1) = gap(z) = 1`. ∎

## 6. Forced-multi inheritance

Suppose, for contradiction, that some optimal circuit `C` for `f` has **≤ 1 reconvergence**.
By §4, `C'` (obtained by contracting the unique gate `g`, a pass-through to `a`) is an
**optimal** circuit for `z` (`opt(z)` gates). We show the contraction does **not increase** the
reconvergence count, so `C'` has ≤ 1 reconvergence — contradicting that `z` is forced-multi
(which forces ≥ 2). This contradiction proves `f` is forced-multi.

*The contraction is non-increasing.* **Convention (corrected 2026-08-19):** fan-out is the number of
**distinct consumer gates**, and the output is **not** a consumer — this is what the encoder
implements (`zc_certify.py`, `build_amo_shared`: one indicator `u[(i,j)]` per consumer gate `j`, and
`z[i]` forced only by two *distinct* `j`). The earlier wording here said edge-occurrences with the
output as a consumer; formalising the definitions in Lean showed that is not the encoder's counting
(`formal/ThresholdTree.lean`, `sharing_defs_differ`). Nothing downstream moves — see the correction in
§2.1 of the paper for why the readings coincide on size-optimal circuits — but the case "`g` is the
output" is now separate: there `|S_g| = 0`, contracting `g` makes `a` the output, `a` loses a consumer,
and `g` (fan-out 0, never a reconvergence) disappears, so the count cannot rise. Assume below that `g`
is not the output. Let `g` have consumer set `S_g` (`|S_g| = fan-out(g) ≥ 1`).
Contracting `g` (pass-through to `a`) removes `g` and makes every consumer in `S_g` read `a`.
Only `a`'s fan-out changes: from `deg(a)` to `deg(a) − 1 + |S_g|` (it loses `g`, gains `S_g`) —
and if some consumer already reads both `a` and `g`, distinct-consumer counting makes this an
*upper* bound, which only helps. Compare reconvergence counts (a node counts iff it is an
internal gate with fan-out ≥ 2):

- **`|S_g| = 1`:** `a`'s fan-out is unchanged (`deg(a) − 1 + 1 = deg(a)`); `g` had fan-out 1,
  so it was not a reconvergence. Count unchanged.
- **`|S_g| ≥ 2` and `deg(a) ≥ 2`:** `a` was already a reconvergence and stays one; `g` (a
  reconvergence) is removed. Count drops by 1.
- **`|S_g| ≥ 2` and `deg(a) = 1`:** `a` was not a reconvergence (fan-out 1, i.e. it fed only
  `g`) and becomes one (fan-out `|S_g| ≥ 2`); `g` (a reconvergence) is removed. Net 0.
- **`a` is an input or constant, not a gate:** the newly high fan-out lands on `a`, which does
  not count; `g` is removed. Count does not increase.

In every case `reconv(C') ≤ reconv(C) ≤ 1`. But `C'` is an `opt(z)`-gate circuit for `z`, and
`z` is forced-multi, so `reconv(C') ≥ 2`. Contradiction. Hence every optimal `C` for `f` has
≥ 2 reconvergences: `f` is forced-multi. ∎

**Machine-checked (2026-08-19).** The non-increase claim above — the whole "*the contraction is
non-increasing*" block — is now `numReconv_contract_le` in `formal/ThresholdTree.lean`, proved with
kernel axioms only. The four bullets survive as the two cases of the Lean proof: away from `a` the
fan-out can only fall, and at `a` it is paid for either by the released edge (`|S_g| = 1`) or by `g`'s
own disappearance from the count (`|S_g| ≥ 2`).

One thing the formalisation caught. The step `deg(a) → deg(a) − 1 + |S_g|` uses **`g ∈ C_a`** — the
contracted gate is itself a consumer of `a`, and stops being one. The prose above says it ("it loses
`g`"); the first Lean statement did not carry it as a hypothesis and was therefore **false**. Four gates
suffice to break it: with `n = 1`, let `w₁` and `w₂` each have exactly one consumer and let `w₂` *not*
read `w₁`; contracting `w₂` into `w₁` hands `w₁` two distinct consumers and the count rises from 0 to 1
(`contract_needs_refs`, axiom-free). The corrected statement requires `refsWire (gs.get p) a`, which is
what `IsPassThrough` delivers semantically. Nothing in the argument of this note changes — the omission
was in the formal statement, not in the proof.

**A second defect, in the definition rather than the statement (same day).** The contraction is only
sound *up to the inversion of the pass-through*: if `g = AND(¬w_a, x)` then under `σ : x = 1` the gate
carries `¬val(a)`, and rewiring `g`'s consumers to `a` must flip the polarity of those edges. The first
Lean definition of `contract` did not, so contracting an inverted pass-through changed the computed
function — and not by a global inversion the free output negation would absorb. Three gates suffice
(`contract_needs_polarity`). The inversion is now a parameter of the contraction. Note that the
*combinatorial* lemma was blind to this: fan-out reads wire indices, never polarities. Proving one half
said nothing about the definition the other half needs.

**A third defect, this one a missing case (2026-08-20).** Contracting a gate renumbers the wires above it,
so the contracted circuit's output is whichever gate was second-to-last. If the contracted gate `g` is
**not** the output, that is the old output and the function is preserved unchanged. If `g` **is** the
output — which is precisely what §5.5 produces in the lift direction, since restricting `x = 1` in
`z ∧ x` turns the *output* gate into the pass-through — the new output is the previous gate, which in
general is unrelated to `a`. Two gates break it (`contract_needs_nonoutput`). So the output case is not a
corner to exclude but a case to state, and it holds exactly when `a` is the wire of that previous gate;
there the function is recovered up to `inv`. Both cases are now proved
(`circuitOut_contract`, `circuitOut_contract_output`), and with the combinatorial half this closes §6 of
this note in Lean.

Worth noting for §5.5: the argument there must therefore say **which** gate the restriction contracts and
where `a` sits, not merely that a pass-through appears. In the lift direction it is the output gate and
`a` is the top gate of `z`'s circuit — the hypothesis holds. In the direction that starts from an
arbitrary optimal circuit for `f`, the gate reading `x` can be anywhere, and if it is the output then `a`
must be shown to be the previous gate. That is a real obligation on §5.5, surfaced by the formalisation.

*Update 2026-08-20.* Two of §5.5(a)'s three parts are now separated, and one is discharged. **Existence**
of a reader of `x_new` is machine-checked (`exists_reader_of_liftAnd`), and it does not come from the
counting argument at all: if nothing read `x_new`, dropping the variable would yield the same circuit over
`n` inputs, so the output could not depend on `x_new`. The hypothesis `z` not identically `0` is load-
bearing — for `z ≡ 0` the constant-false circuit computes `A z` reading nothing.

For **uniqueness**, the two-reader case has to become a construction, and the obligation above turns out
to be vacuous in exactly that case: contract the reader of *smallest* index and it cannot be the output,
since a second reader `q` gives `p < q < m`. Two supporting facts are checked — contracting one reader
leaves the others reading `x_new` (`second_reader_survives`), and the semantic lemmas of §5.7 are already
pointwise in the assignment, so they apply on the slice `x_new = 1`, which is the only place a reader is a
pass-through. The residue is therefore narrower than "§5.5(a)": it is the single-reader-at-the-output case
plus positivity.

*Plan corrected the same day.* Trying to discharge the positional hypothesis produced a counterexample
to the **formal** lower bound, and the obstruction sits in the model, not in the proof. `circuitOut`
returns the last gate, so the model cannot express the zero-gate circuit that returns an input; on the
formula side `Frm` has a `.var` leaf and a literal costs `0`. For `z` a literal: `tree(z) = 0`,
`opt(z) = 1`, and `opt(A z) = 1` rather than `2` (`lift_fails_on_literal`,
`model_asymmetric_on_literal`). In the convention this note uses, a literal costs `0` and `1 = 0 + 1`:
**the mathematics here does not move.** What moves is the status of the positional hypothesis — it is
**necessary in this model**, not a residue of an unfinished proof, and what it excludes is exactly the
literal. `lift_lemma` escapes through its gap hypothesis (`0 = 2`), by accident rather than by design.

Route chosen: keep the model and carry "`z` is not a literal" as an explicit hypothesis where the lower
bound needs it, rather than give the model an output selector and re-audit everything that reads
`circuitOut` — the same reasoning that settled the constant-wire question the same way. One obligation
then remained: the truncation case, a sole reader at the output whose other input is a **gate** wire,
where the prefix up to that gate already agrees on the slice. That case is now machine-checked
(`slice_trunc_lower`): nothing is contracted, the prefix is truncated, it does not read `x_new` because
the only reader was the output, and dropping the variable gives a circuit over `n` inputs with at most
`m − 1` gates. The two output subcases therefore exhaust each other — gate wire is the truncation,
input wire is where the model charges a literal one gate too many — and a non-vacuity control pins that
the hypotheses are satisfiable and the bound tight.

*And the counting argument closed the same day.* `uniq_reader`: two distinct gates reading `x_new` force
`opt(z) + 2 ≤ m`, contradicting the §5.2 upper bound on an optimal circuit. The induction contracts one
reader at a time, always one that is not the output — extracted from the reader count of the `dropLast`
prefix, so no minimality and no `Nat.find`, which is Mathlib-only and unavailable here. It terminates in
the three places above. The lower bound then holds in the form this note wanted: `opt(z) + 1 ≤ m` for any
circuit computing `A z`, with no positional hypothesis (`opt_liftAnd_lower_nopos`).

**And positivity turned out to need dispensing with rather than proving.** A reader whose only edge to
`x_new` is inverted, or which points there with both edges, is constant on the slice — the paper's own
case analysis, carried out with no hypothesis. A gate constant on the slice also yields a smaller
slice-agreeing circuit, through the cascade: no consumer means it is dead and drops; a consumer of a
constant is itself constant on the slice (recurse at a strictly larger index) or a pass-through there.

The shape that makes it one induction: **every branch produces a strictly smaller circuit that still
agrees with `z` on the slice.** Contraction, dead-gate removal and truncation all become instances, and
truncation in that form no longer needs the prefix to be reader-free.

**§5.3 is closed:** `opt(A z) = opt(z) + 1`, machine-checked, no hypothesis on the readers at all.

**And §5.6 closed the same day.** `tree_liftAnd`: `tree(A z) = tree(z) + 1`. The design there follows
from the type: `Frm` has a `.one` leaf but no false constant and no negation node, so restricting
`x_new := 1` returns either a formula-with-polarity or a constant, said explicitly — the polarity travels
in the result because synthesising a negation would cost the very gates being counted. The saved gate
comes from the formula having to mention `x_new`, whose node then collapses.

**Three of the four conclusions are machine-checked with no change to the statement**, because the gap
hypothesis already excludes literals on its own: a literal has `tree = 0` and `opt = 1` in this model, so
`tree(z) = opt(z) + 1` would read `0 = 2`.

**And the forcedness transfer closed, so the `∧` case of this note is machine-checked end to end** (§7, the `∨` case, remains a paper proof — see the scope note below). The circuit for `z`
extracted from the descent has exactly `opt(z)` gates — hence is optimal — and carries no more
reconvergences than the circuit for `A z` it came from, so `ForcedMulti z` transfers upward. That needed
a reconvergence bound for each of the three size-reducing operations rather than for contraction alone;
dead-gate removal came for free, since it *is* a contraction with a freely chosen recipient.

One statement written along the way was false: `dropVar` preserves fan-out only for wires other than
`x_new`, because for `n = 0` the dropped wire collapses onto gate `0`'s wire. That is the same reason the
semantic lemma already carried the no-reader side condition, so the two agree — and the boundary is
pinned by a counterexample rather than left as a remark.

**`lift_lemma` has no `sorry`.** The Lift Lemma is machine-checked under exactly the hypotheses stated
here, in the formalisation's model.

*Scope, stated because an earlier version of this note overstated it (Codex review, 2026-08-20).* As of
2026-08-20 what was machine-checked was the **`∧` case**, and two steps remained paper proofs: §7 below
(the `∨` case) and the convention bridge.

**Update 2026-08-21: §7 is machine-checked** (`lift_lemma_or`; `lift_lemma_both` is the statement
entire, both halves). It went by the **parenthetical** route of §7, not the verbatim one: rather than
replaying §2–6 with the polarity flipped, the formalisation proves the two symmetries the parenthesis
appeals to and lets the `∧` case do the work. `liftOr z = ¬(liftAnd (¬z) ∘ negLast)` pointwise;
output negation is free by construction, because `CircuitComputes` and `FormulaComputes` are
disjunctions over both polarities, so the set of circuits is unchanged; and negating an input is
flipping the polarity of the edges that read that wire, which leaves `ia`/`ib` alone, so `fanOut` and
`numReconv` are identical and "inversions do not change the gate DAG" is now a theorem
(`numReconv_negIn`) rather than an appeal. One place the duality is not free, and the note should say
it: on the formula side a leaf `.var i` has no parent edge to carry the polarity, so the transformation
returns a flip flag which the free output inversion absorbs at the root.

**One step remains a paper proof:** the bridge from the formalisation's convention (the output is the
last gate) to the paper's (a designated output wire). The two agree except on literals, and that
argument is about the *relation* between model and convention, so no statement inside the model can
settle it. It is not a hole in the mathematics; it is a paper step, and an earlier sentence here counted
it as none.

## 7. The `∨` case

For `f = z ∨ x`, restrict `σ : x = 0` instead; then `f|σ = z ∨ 0 = z`. The unique gate reading
`x` becomes a pass-through under `x = 0` when it reads `¬x` (and a constant, forcing a cascade,
when it reads `x` — ruled out exactly as in §4(a)). Every step of §2–6 goes through verbatim
with the polarity flipped. (Equivalently, `z ∨ x = ¬(¬z ∧ ¬x)`, and free input/output
inversions give `opt`, `tree`, `gap`, and the reconvergence structure of `¬z ∧ ¬x`, to which
the `∧` case applies since `¬z` is forced-multi gap=1 iff `z` is — inversions do not change
the gate DAG.) ∎

This completes the proof of the Lift Lemma. ∎∎

---

## The Lift Theorem (unconditional)

The gap=1, forced-multiple-reconvergence functions of this note are the **forced-reconvergence family**
 — named for the gap framework of arXiv:2603.08033 in which they live and the
characterization here; earlier drafts denoted them `Z`.

> **Lift Theorem.** For every `n ≥ 4` there exists a Boolean function on `n` variables that is
> gap=1 and forced-multi — i.e. the forced-reconvergence family is non-empty at every `n ≥ 4`.

**Proof.** Claim 0034 exhibits a gap=1 forced-multi function `z₄` at `n = 4` (e.g. the
flagship `0x03de`, opt=6, tree=7, forced-multi UNSAT DRAT-certified). Define
`z_{n+1} := z_n ∧ x_{n+1}`. By the Lift Lemma each `z_n` is gap=1 and forced-multi at `n`
variables. ∎

This turns the conditional "Consequence" of `technote_z_generalization.md` into a theorem: the
forced-reconvergence phenomenon is genuinely infinite, not an artifact of `n = 4`.

---

## Corroboration (independent of the proof)

- **n = 3 exhaustive** (`lift_lemma_empirical_test.py`, opt sweep): `opt(z∧x)=opt(z)+1` and
  `opt(z∨x)=opt(z)+1` over **all 218 essential `n=3` functions** — 0 violations, 0 inconclusive.
  This exhaustively corroborates the lower bound of §3.
- **n = 4 → 5 → 6 DRAT witnesses:** `0x03de` → `0x03de0000` → `0x3de000000000000`, each
  gap=1 forced-multi, all `s VERIFIED` (SHAs in `certs/`, ledger claim 0035).
- **Forced-multi inheritance probe** (`lift_lemma_empirical_test.py` test 3): over the six n=4
  forced-reconvergence classes lifted to n=5, **0 lost forced-multi** — `0x03de∧x4` and `0x03de∨x4` both certify
  forced-multi (at-most-one-shared UNSAT); the rest time out (SAT at n=5 is heavy) without any
  flipping to not-forced-multi. Corroborates §6.

*Note on the elimination step.* A restriction-based "gate count" probe that flags only gates
becoming **constant** will report zero eliminations here, because the eliminated gate `g`
becomes a **pass-through** (`g|σ = a`, non-constant but structurally redundant), not a constant
— exactly the distinction handled in §2 ("a pass-through gate is spliced out"). This is why the
proof's elimination is structural (splicing redundant pass-throughs), not semantic (collapsing
to constants); a constant-only probe is not a faithful test of §4 and is not used as evidence.

These are corroboration, not part of the proof; the proof above is self-contained.
