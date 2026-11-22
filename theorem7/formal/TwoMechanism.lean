import LiftTower

namespace TwoMechanism
open ThresholdTree

def TwoMechanism (n : Nat) : Prop :=
  ∀ (f : Func n) (m : Nat), Gap f 1 → IsOpt f m →
    ∀ gs : List Gate, wfC n gs → gs.length = m → CircuitComputes gs f →
      numReconv n gs = 1 ∧ ∀ p, p < gs.length → 2 ≤ fanOut n gs p → fanOut n gs p = 2

def SomeOptimumSharesAtMostOnce (n : Nat) : Prop :=
  ∀ f : Func n, Gap f 1 →
    ∃ m gs, IsOpt f m ∧ wfC n gs ∧ gs.length = m ∧ CircuitComputes gs f ∧ numReconv n gs ≤ 1

theorem isOpt_unique {n : Nat} {f : Func n} {m m' : Nat} (h : IsOpt f m) (h' : IsOpt f m') :
    m = m' := by
  have h1 := h.2 m' h'.1
  have h2 := h'.2 m h.1
  omega

theorem exists_opt_circuit {n : Nat} {f : Func n} {m : Nat} (h : IsOpt f m) :
    ∃ gs : List Gate, wfC n gs ∧ gs.length = m ∧ CircuitComputes gs f := by
  obtain ⟨gs, hwf, hle, hc⟩ := h.1
  have hge : m ≤ gs.length := h.2 gs.length ⟨gs, hwf, Nat.le_refl _, hc⟩
  exact ⟨gs, hwf, by omega, hc⟩

theorem not_someOptimum_of_forcedMulti {n : Nat} (f : Func n) (hg : Gap f 1)
    (hF : ForcedMulti f) : ¬ SomeOptimumSharesAtMostOnce n := by
  intro hS
  obtain ⟨m, gs, hopt, hwf, hlen, hc, hle⟩ := hS f hg
  obtain ⟨m', hopt', hall⟩ := hF
  have hm : m = m' := isOpt_unique hopt hopt'
  have h2 := hall gs hwf (by omega) hc
  omega

theorem not_twoMechanism_of_forcedMulti {n : Nat} (f : Func n) (hg : Gap f 1)
    (hF : ForcedMulti f) : ¬ TwoMechanism n := by
  intro hT
  obtain ⟨m, t, hopt, ht, hmt⟩ := hg
  obtain ⟨gs, hwf, hlen, hc⟩ := exists_opt_circuit hopt
  have h1 := (hT f m ⟨m, t, hopt, ht, hmt⟩ hopt gs hwf hlen hc).1
  obtain ⟨m', hopt', hall⟩ := hF
  have hm : m = m' := isOpt_unique hopt hopt'
  have h2 := hall gs hwf (by omega) hc
  omega

theorem theorem7_false_n4 : ¬ TwoMechanism 4 :=
  not_twoMechanism_of_forcedMulti Witness4.z03de Witness4.z03de_gap1
    Witness4Forced.z03de_forcedMulti

theorem someOptimum_false_n4 : ¬ SomeOptimumSharesAtMostOnce 4 :=
  not_someOptimum_of_forcedMulti Witness4.z03de Witness4.z03de_gap1
    Witness4Forced.z03de_forcedMulti

theorem theorem7_false (n : Nat) (hn : 4 ≤ n) : ¬ TwoMechanism n := by
  obtain ⟨f, _m, _hdep, _hopt, _htree, hg, hF⟩ :=
    LiftTower.forced_family_nonempty_at_every_arity n hn
  exact not_twoMechanism_of_forcedMulti f hg hF

theorem someOptimum_false (n : Nat) (hn : 4 ≤ n) : ¬ SomeOptimumSharesAtMostOnce n := by
  obtain ⟨f, _m, _hdep, _hopt, _htree, hg, hF⟩ :=
    LiftTower.forced_family_nonempty_at_every_arity n hn
  exact not_someOptimum_of_forcedMulti f hg hF

#print axioms not_twoMechanism_of_forcedMulti
#print axioms not_someOptimum_of_forcedMulti
#print axioms theorem7_false_n4
#print axioms someOptimum_false_n4
#print axioms theorem7_false
#print axioms someOptimum_false

end TwoMechanism
