# The Lift Lemma — a full proof

> A complete proof of the lift lemma and its unconditional consequence: **forced-multiple-
> reconvergence gap=1 (forced-reconvergence family) functions exist for every n ≥ 4.** Self-contained; the encoder
> it refers to is in `../encoder/`, and the certificates it refers to are reproduced by `../VERIFY.md`.

## Model and definitions

We work in the And-Inverter Graph (AIG) model over the basis U₂ (see `../encoder/aig_exact.py`):

- A **circuit** is a DAG. Sources are the input variables `x₁,…,x_n` and the constant `1`.
  Every internal node is a **2-input AND gate**. Every edge and the output may be freely
  inverted (inversions are free — they cost nothing).
- `opt(f)` = minimum number of AND gates in a circuit computing `f`.
- A **formula** (tree) is a circuit in which every *gate* has fan-out exactly 1 (input
  variables may be reused). `tree(f)` = minimum number of AND gates in a formula for `f`.
- `gap(f) = tree(f) − opt(f) ≥ 0`.
- A **reconvergence** is an internal AND gate consumed by ≥ 2 distinct gates — fan-out ≥ 2 counting
  **distinct consuming gates** (the circuit output counts as one consumer); inputs do not count.
  This matches the at-most-one-shared encoding in `../encoder/n5_forced_test.py`, whose sharing
  variable `u[i,j]` fires once per consuming gate `j`, regardless of operand-edge multiplicity.
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

*The contraction is non-increasing.* **Convention:** fan-out counts **distinct consuming gates**
(with the circuit output as one consumer) — the same measure the encoding uses; thus every used
gate has fan-out ≥ 1, and the case "`g` is the output" is just `|S_g| ≥ 1` with the output terminal
among `g`'s consumers (after contraction the output reads `a`). In a size-optimal circuit no gate
takes the same source for both inputs (operand order `a<b`, and a doubled input would waste a
gate), so a gate consumes `g` at most once and edge-multiplicity never arises. Let `g` have
consumer set `S_g` (`|S_g| = fan-out(g)`).
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

The gap=1, forced-multiple-reconvergence functions of this note are called the **forced-reconvergence family**
(earlier drafts denoted them `Z`). They live in the gap
framework of arXiv:2603.08033.

> **Lift Theorem.** For every `n ≥ 4` there exists a Boolean function on `n` variables that is
> gap=1 and forced-multi — i.e. the forced-reconvergence family is non-empty at every `n ≥ 4`.

**Proof.** A gap=1 forced-multi function `z₄` exists at `n = 4`: the flagship `0x03de`
(opt=6, tree=7, forced-multi), reproducible from scratch via
`../verify/reproduce_witness.py 0x03de 6 --full`. Define
`z_{n+1} := z_n ∧ x_{n+1}`. By the Lift Lemma each `z_n` is gap=1 and forced-multi at `n`
variables. ∎

So this phenomenon is genuinely infinite, not an artifact of `n = 4`.

---

## Corroboration (independent of the proof)

- **n = 3 exhaustive** (opt sweep): `opt(z∧x)=opt(z)+1` and `opt(z∨x)=opt(z)+1` over **all 218
  essential `n=3` functions** — 0 violations, 0 inconclusive. This exhaustively corroborates the
  lower bound of §3.
- **n = 4 → 5 → 6 DRAT witnesses:** `0x03de` → `0x03de0000` → `0x3de000000000000`, each
  gap=1 forced-multi, all `s VERIFIED`.
- **Forced-multi inheritance probe:** over the six n=4 forced-multi classes lifted to n=5, **0 lost
  forced-multi** — `0x03de∧x4` and `0x03de∨x4` both certify forced-multi (at-most-one-shared
  UNSAT); the rest time out (SAT at n=5 is heavy) without any flipping to not-forced-multi.
  Corroborates §6.

*Note on the elimination step.* A restriction-based "gate count" probe that flags only gates
becoming **constant** will report zero eliminations here, because the eliminated gate `g`
becomes a **pass-through** (`g|σ = a`, non-constant but structurally redundant), not a constant
— exactly the distinction handled in §2 ("a pass-through gate is spliced out"). This is why the
proof's elimination is structural (splicing redundant pass-throughs), not semantic (collapsing
to constants); a constant-only probe is not a faithful test of §4 and is not used as evidence.

These are corroboration, not part of the proof; the proof above is self-contained.
