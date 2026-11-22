# Lean 4 proofs: the `0x03de` witness and the Lift Theorem

These four files are the machine-checked part of *Forced Multiple Reconvergence at Unit Gap*
(Zenodo, [doi:10.5281/zenodo.24408786](https://doi.org/10.5281/zenodo.24408786)). The paper cites
them by file name under the layout of the development tree; the file names here are the same.

| file | imports | what it proves |
|---|---|---|
| `ThresholdTree.lean` | nothing (core Lean) | the model: functions, AND-inverter circuits with negated inputs, formulas, `IsOpt`, `IsTree`, `Gap`, fan-out, `ForcedMulti`; Krinkin's Theorem 3 (`threshold`), Theorem 4 restated for non-literals (`tree_thm`), and the upper and lower bounds of the lift (`lift_upper_bounds`, `opt_liftAnd_lower`) |
| `Witness4.lean` | `ThresholdTree` | for `z03de = 0x03de` on 4 inputs: a 6-gate circuit and no 5-gate one (`z03de_isOpt6`), formula size exactly 7 (`z03de_tree`), so `Gap z03de 1` (`z03de_gap1`) |
| `Witness4Forced.lean` | `Witness4` | every 6-gate circuit for `z03de` has at least two gates of fan-out ≥ 2 (`z03de_forcedMulti`), and the AND- and OR-lifts of `z03de` to 5 inputs are forced-multi with gap 1 (`n5_witnesses`) |
| `LiftTower.lean` | `Witness4Forced` | Theorem 5.2 of the paper: for every `n ≥ 4` there is a function of `n` essential variables with gap 1 that is forced-multi (`forced_family_nonempty_at_every_arity`, from `lift_tower`) |
| `Axioms.lean` | `LiftTower` | no new result; prints the axioms each headline theorem depends on |

`ForcedMulti f` reads: `f` has an optimum `m`, and every well-formed circuit of `m` gates that computes
`f` has at least two gates of fan-out ≥ 2. In this model the output is always the last gate, so a
literal has `opt = 1` and `tree = 0`; that is why Theorem 4 appears restated for non-literals.

## Build

Lean 4.33.0, pinned in `lean-toolchain`. No Mathlib, no Lake project: each file compiles with the
plain `lean` binary against the `.olean` of the one before it.

```bash
cd formal
for f in ThresholdTree Witness4 Witness4Forced LiftTower Axioms; do
  LEAN_PATH=. lean -o "$f.olean" "$f.lean" || break
done
```

Measured on the shipped files on 2026-11-21 (Lean 4.33.0, x86-64 Linux, AMD Ryzen 9 9950X, one file at
a time):

| file | wall clock | `sorry` | errors |
|---|---|---|---|
| `ThresholdTree.lean` | 13 s | 0 | 0 |
| `Witness4.lean` | 275 s | 0 | 0 |
| `Witness4Forced.lean` | 3,446 s | 0 | 0 |
| `LiftTower.lean` | 1 s | 0 | 0 |
| `Axioms.lean` | under 1 s | 0 | 0 |

`Witness4.lean` peaks near 11.5 GB of memory: the kernel check of the formula-size lower bound runs a
dynamic program over bitmasks. A machine with 8 GB will not finish it.

## What is trusted beyond the kernel

`Axioms.lean` prints the axioms of twelve headline theorems. Six of them, `threshold`, `tree_thm`,
`lift_upper_bounds`, `opt_liftAnd_lower`, `fanOut_eq_fanOutEdges_of_opt` and `z03de_tree`, depend
only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`; `lift_upper_bounds` does
not even use `Classical.choice`). The other six also depend on two finite facts about `0x03de`
that are decided by `native_decide`, so they trust Lean's compiler as well as its kernel:

- `Witness4.anyC_miss`: an exhaustive search finds no circuit of 1 to 5 gates computing `z03de` or its
  complement. This is the lower half of `opt = 6`, used by `z03de_isOpt6` and `z03de_gap1`.
- `Witness4Forced.allF_hit`: an exhaustive search over 6-gate circuits finds that each one computing
  `z03de` or its complement has at least two gates of fan-out ≥ 2. Its soundness (`allF_sound`) is
  proved in the kernel; this fact is used by `z03de_forcedMulti`, `n5_witnesses`, `lift_tower` and
  `forced_family_nonempty_at_every_arity`.

The formula-size lower bound behind `z03de_tree` used to be a third `native_decide` fact; it is now
checked by the kernel, which is what costs the memory noted above.

## Comments

The files in the development tree carry working notes in their comments. For this bundle the comments
were removed mechanically: `--` to the end of the line and `/- … -/` blocks, nothing else. The
declarations are the same, in the same order, and the files as shipped are the ones that were compiled
for the table above (SHA-256 below).

```
d6f720b6fc5fc3ea6e0458f4ff0d045e0cd8a74f9f83b8932d3924bfbedb477c  ThresholdTree.lean
119aa185a55c952469d9338ead95ad5b82638cd4f41c1e5c48f46a1f360be96c  Witness4.lean
7cbe777a0895776d2fec5b1648f2d203376f9694b6610a4b59b382173f0c05dc  Witness4Forced.lean
cb96c3bb8c529931a78c422713441481591a31c893a087ce7ac7ba438afc9f22  LiftTower.lean
3d750c89320165eb6df245048076225d41bd22604a184825b9b0d824af8a0ddd  Axioms.lean
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  lean-toolchain
```
