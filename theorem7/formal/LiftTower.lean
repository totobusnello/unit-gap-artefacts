import Witness4Forced
set_option maxRecDepth 100000
namespace LiftTower
open ThresholdTree Witness4 Witness4Forced

theorem liftAnd_ne_false (z : Func n) (hz : z ≠ fun _ => false) :
    liftAnd z ≠ fun _ => false := by
  intro hc
  apply hz
  funext y
  have := congrFun hc (snocT y true)
  rw [liftAnd, dropLast_snocT, snocT_last] at this
  simpa using this

theorem liftAnd_ne_true (z : Func n) : liftAnd z ≠ fun _ => true := by
  intro hc
  have h0 := congrFun hc (snocT (fun _ => false) false)
  rw [liftAnd, snocT_last] at h0
  simp at h0

theorem exists_true_of_ne_false (z : Func n) (h : z ≠ fun _ => false) : ∃ y, z y = true := by
  by_cases hc : ∃ y, z y = true
  · exact hc
  · exact absurd (funext fun y => by
      cases hv : z y with
      | false => rfl
      | true  => exact absurd ⟨y, hv⟩ hc) h

private theorem cast_ne_last (i : Fin n) : (i.castSucc : Fin (n+1)) ≠ Fin.last n := by
  intro h
  have : i.val = n := congrArg Fin.val h
  omega

private theorem dropLast_flip_last (x : Assign (n+1)) :
    dropLast (flipAt x (Fin.last n)) = dropLast x := by
  funext i
  simp [dropLast, flipAt, cast_ne_last i]

private theorem dropLast_flip_cast (x : Assign (n+1)) (i : Fin n) :
    dropLast (flipAt x i.castSucc) = flipAt (dropLast x) i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [dropLast, flipAt]
  · have hv : (j.castSucc : Fin (n+1)) ≠ i.castSucc := by
      intro h
      apply hj
      apply Fin.eq_of_val_eq
      have hvv := congrArg Fin.val h
      simpa using hvv
    simp [dropLast, flipAt, hv, hj]

private theorem flip_last_at_last (x : Assign (n+1)) :
    flipAt x (Fin.last n) (Fin.last n) = !x (Fin.last n) := by
  simp [flipAt]

private theorem flip_cast_at_last (x : Assign (n+1)) (i : Fin n) :
    flipAt x i.castSucc (Fin.last n) = x (Fin.last n) := by
  simp [flipAt, Ne.symm (cast_ne_last i)]

theorem liftAnd_essential_last (z : Func n) (h0 : z ≠ fun _ => false) :
    dependsOn (liftAnd z) (Fin.last n) := by
  obtain ⟨y, hy⟩ := exists_true_of_ne_false z h0
  refine ⟨snocT y true, ?_⟩
  rw [liftAnd, liftAnd, dropLast_flip_last, flip_last_at_last, dropLast_snocT, snocT_last, hy]
  simp

theorem liftAnd_essential_cast (z : Func n) (i : Fin n) (h : dependsOn z i) :
    dependsOn (liftAnd z) i.castSucc := by
  obtain ⟨y, hy⟩ := h
  refine ⟨snocT y true, ?_⟩
  rw [liftAnd, liftAnd, dropLast_flip_cast, flip_cast_at_last, dropLast_snocT, snocT_last]
  simpa using hy

theorem lift_tower : ∀ k : Nat, ∃ (f : Func (4 + k)) (m : Nat),
    (f ≠ fun _ => false) ∧ (f ≠ fun _ => true) ∧ (∀ i, dependsOn f i) ∧
      IsOpt f m ∧ IsTree f (m + 1) ∧ Gap f 1 ∧ ForcedMulti f := by
  intro k
  induction k with
  | zero =>
      exact ⟨z03de, 6, z03de_ne_false, z03de_ne_true, z03de_essential, z03de_isOpt6,
        z03de_tree, z03de_gap1, z03de_forcedMulti⟩
  | succ k ih =>
      obtain ⟨f, m, hf0, hf1, hess, hopt, htree, _, hfm⟩ := ih
      obtain ⟨h1, h2, h3, h4⟩ := lift_lemma f m (m + 1) hf0 hf1 hopt htree rfl hfm
      refine ⟨liftAnd f, m + 1, liftAnd_ne_false f hf0, liftAnd_ne_true f, ?_, h1, h2, h3, h4⟩
      intro i

      by_cases hi : i.val < 4 + k
      · have : i = (⟨i.val, hi⟩ : Fin (4 + k)).castSucc := Fin.eq_of_val_eq rfl
        rw [this]; exact liftAnd_essential_cast f _ (hess _)
      · have hlt := i.isLt
        have : i = Fin.last (4 + k) := by
          apply Fin.eq_of_val_eq
          show i.val = (Fin.last (4 + k)).val
          simp [Fin.last]
          omega
        rw [this]; exact liftAnd_essential_last f hf0

theorem forced_family_nonempty_at_every_arity :
    ∀ n : Nat, 4 ≤ n → ∃ (f : Func n) (m : Nat),
      (∀ i, dependsOn f i) ∧ IsOpt f m ∧ IsTree f (m + 1) ∧ Gap f 1 ∧ ForcedMulti f := by
  intro n hn
  obtain ⟨k, hk⟩ := Nat.le.dest hn
  subst hk
  obtain ⟨f, m, _, _, hess, h1, h2, h3, h4⟩ := lift_tower k
  exact ⟨f, m, hess, h1, h2, h3, h4⟩

#print axioms lift_tower
#print axioms forced_family_nonempty_at_every_arity

end LiftTower
