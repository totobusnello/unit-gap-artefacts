import Witness4
set_option maxRecDepth 100000

namespace Witness4Forced
open ThresholdTree Witness4

def covers (a tgt : Nat) : Bool := (a &&& tgt == tgt) || (a &&& nnot true tgt == nnot true tgt)

private theorem and_absorb (a b : Nat) : (a &&& b) &&& a = a &&& b := by
  rw [Nat.and_comm (a &&& b) a, ← Nat.and_assoc, Nat.and_self]

private theorem and_absorb' (a b : Nat) : (a &&& b) &&& b = a &&& b := by
  rw [Nat.and_assoc, Nat.and_self]

theorem covers_left (va vb tgt : Nat) (h : va &&& vb = tgt ∨ va &&& vb = nnot true tgt) :
    covers va tgt = true := by
  rcases h with h | h
  · refine (Bool.or_eq_true _ _).mpr (Or.inl ?_)
    simp only [beq_iff_eq]
    rw [Nat.and_comm va tgt, ← h, and_absorb]
  · refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
    simp only [beq_iff_eq]
    rw [Nat.and_comm va _, ← h, and_absorb]

theorem covers_right (va vb tgt : Nat) (h : va &&& vb = tgt ∨ va &&& vb = nnot true tgt) :
    covers vb tgt = true := by
  rcases h with h | h
  · refine (Bool.or_eq_true _ _).mpr (Or.inl ?_)
    simp only [beq_iff_eq]
    rw [Nat.and_comm vb tgt, ← h, and_absorb']
  · refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
    simp only [beq_iff_eq]
    rw [Nat.and_comm vb _, ← h, and_absorb']

def wiresCov (acc : List Nat) (tgt : Nat) : List (Nat × Bool) :=
  (List.range (wireCount acc)).flatMap (fun a =>
    (([false, true] : List Bool)).filterMap (fun pa =>
      if covers (nnot pa (wAt acc a)) tgt then some (a, pa) else none))

theorem mem_wiresCov (acc : List Nat) (tgt a : Nat) (pa : Bool) (ha : a < wireCount acc)
    (hc : covers (nnot pa (wAt acc a)) tgt = true) : (a, pa) ∈ wiresCov acc tgt := by
  refine List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, ?_⟩
  refine List.mem_filterMap.mpr ⟨pa, ?_, ?_⟩
  · cases pa <;> simp
  · rw [if_pos hc]

def optsLast (acc : List Nat) (tgt : Nat) : List (Gate × Nat) :=
  (wiresCov acc tgt).flatMap (fun p1 =>
    (wiresCov acc tgt).filterMap (fun p2 =>
      if p1.1 ≤ p2.1 then
        some ((⟨p1.2, p1.1, p2.2, p2.1⟩ : Gate), gAnd p1.2 (wAt acc p1.1) p2.2 (wAt acc p2.1))
      else none))

theorem mem_optsLast (acc : List Nat) (tgt : Nat) (na nb : Bool) (a b : Nat)
    (ha : a < wireCount acc) (hb : b < wireCount acc) (hab : a ≤ b)
    (hca : covers (nnot na (wAt acc a)) tgt = true)
    (hcb : covers (nnot nb (wAt acc b)) tgt = true) :
    ((⟨na, a, nb, b⟩ : Gate), gAnd na (wAt acc a) nb (wAt acc b)) ∈ optsLast acc tgt := by
  refine List.mem_flatMap.mpr ⟨(a, na), mem_wiresCov acc tgt a na ha hca, ?_⟩
  refine List.mem_filterMap.mpr ⟨(b, nb), mem_wiresCov acc tgt b nb hb hcb, ?_⟩
  rw [if_pos hab]

def allF : Nat → List Gate → List Nat → Nat → Bool
  | 0, _, _, _ => true
  | 1, pre, acc, tgt =>
      (optsLast acc tgt).all (fun gv =>
        if gv.2 == tgt || gv.2 == nnot true tgt then
          decide (2 ≤ numReconv 4 (pre ++ [gv.1]))
        else true)
  | k + 2, pre, acc, tgt =>
      (optsAt acc).all (fun gv =>
        redundant acc gv.2 || allF (k + 1) (pre ++ [gv.1]) (acc ++ [gv.2]) tgt)

theorem allF_sound : ∀ (suf pre : List Gate) (tgt : Nat),
    wfC 4 (pre ++ suf) → suf ≠ [] → NormFrom pre suf →
    ((ttsOf (pre ++ suf)).getD ((pre ++ suf).length - 1) 0 = tgt
      ∨ (ttsOf (pre ++ suf)).getD ((pre ++ suf).length - 1) 0 = nnot true tgt) →
    allF suf.length pre (ttsOf pre) tgt = true →
    2 ≤ numReconv 4 (pre ++ suf) := by
  intro suf
  induction suf with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons g rest ih =>
    intro pre tgt hwf _ hnorm hval hall
    have hb := wfC_head pre g rest hwf
    have hlen : (ttsOf pre).length = pre.length := length_ttsOf pre
    have hle : g.ia ≤ g.ib := by
      cases rest with
      | nil => exact hnorm
      | cons g2 r2 => exact hnorm.1
    cases rest with
    | nil =>
      rw [last_tt pre g] at hval
      have hcov : ∀ side : Bool,
          covers (nnot (if side then g.nb else g.na)
            (wAt (ttsOf pre) (if side then g.ib else g.ia))) tgt = true := by
        intro side
        cases side
        · exact covers_left _ _ tgt hval
        · exact covers_right _ _ tgt hval
      have hmem : ((⟨g.na, g.ia, g.nb, g.ib⟩ : Gate),
          gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) ∈
          optsLast (ttsOf pre) tgt := by
        refine mem_optsLast (ttsOf pre) tgt g.na g.nb g.ia g.ib ?_ ?_ hle (hcov false) (hcov true)
        · rw [wireCount, hlen]; exact hb.1
        · rw [wireCount, hlen]; exact hb.2
      have hone : allF 1 pre (ttsOf pre) tgt = true := hall
      have hthis := (List.all_eq_true.mp hone) _ hmem
      have hcond : (gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib) == tgt
          || gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)
              == nnot true tgt) = true := by
        rcases hval with h | h
        · simp [h]
        · simp [h]
      rw [if_pos hcond] at hthis
      exact of_decide_eq_true hthis
    | cons g2 r2 =>
      obtain ⟨-, hred, hnorm'⟩ := hnorm
      have hcat : pre ++ g :: g2 :: r2 = (pre ++ [g]) ++ (g2 :: r2) := by simp
      have hmem : ((⟨g.na, g.ia, g.nb, g.ib⟩ : Gate),
          gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) ∈
          optsAt (ttsOf pre) := by
        refine mem_optsAt (ttsOf pre) g.na g.nb g.ia g.ib ?_ ?_ hle
        · rw [wireCount, hlen]; exact hb.1
        · rw [wireCount, hlen]; exact hb.2
      have hstep : allF (r2.length + 2) pre (ttsOf pre) tgt = true := hall
      have hthis := (List.all_eq_true.mp hstep) _ hmem
      simp only [hred, Bool.false_or] at hthis
      rw [← ttsOf_concat] at hthis
      have hres := ih (pre ++ [g]) tgt (by rw [← hcat]; exact hwf) (by simp) hnorm'
        (by rw [← hcat] at *; exact hval) (by simpa using hthis)
      rw [← hcat] at hres
      exact hres

theorem refsWire_normGate (g : Gate) (w : Nat) : refsWire (normGate g) w = refsWire g w := by
  obtain ⟨na, ia, nb, ib⟩ := g
  unfold normGate
  split
  · rfl
  · simp only [refsWire]
    exact Bool.or_comm _ _

theorem fanOut_normC (gs : List Gate) (p : Nat) : fanOut 4 (normC gs) p = fanOut 4 gs p := by
  unfold fanOut normC
  rw [List.countP_map]
  exact List.countP_congr (fun g _ => by
    simp only [Function.comp_apply]
    rw [refsWire_normGate])

theorem numReconv_normC (gs : List Gate) : numReconv 4 (normC gs) = numReconv 4 gs := by
  unfold numReconv
  rw [length_normC]
  exact List.countP_congr (fun p _ => by rw [fanOut_normC])

theorem allF_hit : allF 6 [] [] (ttN z03de) = true := by native_decide

theorem z03de_forcedMulti : ForcedMulti z03de := by
  refine ⟨6, z03de_isOpt6, ?_⟩
  intro gs hwf0 hlen hc0
  have hwf : wfC 4 (normC gs) := wfC_normC gs hwf0
  have hlenN : (normC gs).length = 6 := by rw [length_normC]; exact hlen
  have hc : CircuitComputes (normC gs) z03de := circuitComputes_normC gs z03de hc0
  have hne : normC gs ≠ [] := by
    intro h
    rw [h] at hlenN
    simp at hlenN
  have hnorm : NormFrom [] (normC gs) :=
    normFrom_of_opt z03de (normC gs) 6 z03de_ne_false z03de_ne_true hwf z03de_isOpt6 hlenN hc
      (mem_normC_le gs) (normC gs) [] (by simp)
  have hval := tt_out (normC gs) hwf hne z03de hc
  have hres := allF_sound (normC gs) [] (ttN z03de) (by simpa using hwf) hne hnorm
    (by simpa using hval) (by rw [hlenN]; exact allF_hit)
  rw [← numReconv_normC gs]
  simpa using hres

def asg5 (t : Nat) : Assign 5 := fun i => (t >>> i.val) % 2 == 1

theorem dropLast_asg5 (t : Nat) : dropLast (asg5 t) = asg t := by
  funext i
  rfl

theorem last_asg5 (t : Nat) : asg5 t (Fin.last 4) = ((t >>> 4) % 2 == 1) := rfl

theorem liftAnd_z03de_tt :
    (List.range 32).all (fun t =>
      liftAnd z03de (asg5 t) == (((0x03de0000 : Nat) >>> t) % 2 == 1)) = true := by
  decide

theorem liftOr_z03de_tt :
    (List.range 32).all (fun t =>
      liftOr z03de (asg5 t) == (((0xffff03de : Nat) >>> t) % 2 == 1)) = true := by
  decide

theorem n5_witnesses :
    ((List.range 32).all (fun t =>
        liftAnd z03de (asg5 t) == (((0x03de0000 : Nat) >>> t) % 2 == 1)) = true
      ∧ IsOpt (liftAnd z03de) 7 ∧ IsTree (liftAnd z03de) 8 ∧
        Gap (liftAnd z03de) 1 ∧ ForcedMulti (liftAnd z03de))
    ∧ ((List.range 32).all (fun t =>
        liftOr z03de (asg5 t) == (((0xffff03de : Nat) >>> t) % 2 == 1)) = true
      ∧ IsOpt (liftOr z03de) 7 ∧ IsTree (liftOr z03de) 8 ∧
        Gap (liftOr z03de) 1 ∧ ForcedMulti (liftOr z03de)) := by
  obtain ⟨⟨ha1, ha2, ha3, ha4⟩, ⟨hb1, hb2, hb3, hb4⟩⟩ :=
    lift_lemma_both z03de 6 7 z03de_ne_false z03de_ne_true z03de_isOpt6 z03de_tree rfl
      z03de_forcedMulti
  exact ⟨⟨liftAnd_z03de_tt, ha1, ha2, ha3, ha4⟩, ⟨liftOr_z03de_tt, hb1, hb2, hb3, hb4⟩⟩

#print axioms covers_left
#print axioms refsWire_normGate
#print axioms numReconv_normC
#print axioms allF_sound
#print axioms liftAnd_z03de_tt
#print axioms liftOr_z03de_tt
#print axioms allF_hit
#print axioms z03de_forcedMulti
#print axioms n5_witnesses

end Witness4Forced
