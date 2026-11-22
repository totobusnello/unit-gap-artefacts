namespace ThresholdTree

variable {n : Nat}

abbrev Assign (n : Nat) := Fin n → Bool

abbrev Func (n : Nat) := Assign n → Bool

def flipAt (x : Assign n) (i : Fin n) : Assign n :=
  fun j => if j = i then !x j else x j

def dependsOn (f : Func n) (i : Fin n) : Prop :=
  ∃ x, f x ≠ f (flipAt x i)

structure Gate where
  na : Bool
  ia : Nat
  nb : Bool
  ib : Nat

def wireVal (x : Assign n) (vals : Array Bool) (i : Nat) : Bool :=
  if h : i < n then x ⟨i, h⟩ else vals.getD (i - n) false

def evalGates (x : Assign n) (gs : List Gate) : Array Bool :=
  gs.foldl
    (fun vals g =>
      vals.push ((xor g.na (wireVal x vals g.ia)) && (xor g.nb (wireVal x vals g.ib))))
    #[]

def circuitOut (x : Assign n) (gs : List Gate) : Bool :=
  (evalGates x gs).getD (gs.length - 1) false

def wfC (n : Nat) (gs : List Gate) : Prop :=
  ∀ p : Fin gs.length, (gs.get p).ia < n + p.val ∧ (gs.get p).ib < n + p.val

def CircuitComputes (gs : List Gate) (f : Func n) : Prop :=
  (∀ x, circuitOut x gs = f x) ∨ (∀ x, circuitOut x gs = !(f x))

def HasCircuit (f : Func n) (k : Nat) : Prop :=
  ∃ gs : List Gate, wfC n gs ∧ gs.length ≤ k ∧ CircuitComputes gs f

def IsOpt (f : Func n) (m : Nat) : Prop :=
  HasCircuit f m ∧ ∀ k, HasCircuit f k → m ≤ k

inductive Frm (n : Nat) where
  | var : Fin n → Frm n
  | one : Frm n
  | and : Bool → Frm n → Bool → Frm n → Frm n

def evalF : Frm n → Func n
  | .var i => fun x => x i
  | .one => fun _ => true
  | .and pa a pb b => fun x => (xor pa (evalF a x)) && (xor pb (evalF b x))

def gatesF : Frm n → Nat
  | .var _ => 0
  | .one => 0
  | .and _ a _ b => 1 + gatesF a + gatesF b

def FormulaComputes (φ : Frm n) (f : Func n) : Prop :=
  (evalF φ = f) ∨ (evalF φ = fun x => !(f x))

def HasFormula (f : Func n) (k : Nat) : Prop :=
  ∃ φ : Frm n, gatesF φ ≤ k ∧ FormulaComputes φ f

def IsTree (f : Func n) (t : Nat) : Prop :=
  HasFormula f t ∧ ∀ k, HasFormula f k → t ≤ k

def refsWire (g : Gate) (w : Nat) : Bool := g.ia == w || g.ib == w

def edgesTo (g : Gate) (w : Nat) : Nat :=
  (if g.ia == w then 1 else 0) + (if g.ib == w then 1 else 0)

def fanOut (n : Nat) (gs : List Gate) (p : Nat) : Nat :=
  gs.countP (fun g => refsWire g (n + p))

def fanOutEdges (n : Nat) (gs : List Gate) (p : Nat) : Nat :=
  (gs.map (fun g => edgesTo g (n + p))).sum

def IsReconv (n : Nat) (gs : List Gate) (p : Nat) : Prop := 2 ≤ fanOut n gs p

def numReconv (n : Nat) (gs : List Gate) : Nat :=
  (List.range gs.length).countP (fun p => decide (2 ≤ fanOut n gs p))

def NoSharing (n : Nat) (gs : List Gate) : Prop := ∀ p, fanOut n gs p ≤ 1

def ForcedMulti (f : Func n) : Prop :=
  ∃ m, IsOpt f m ∧
    ∀ gs : List Gate, wfC n gs → gs.length = m → CircuitComputes gs f →
      2 ≤ numReconv n gs

def Gap (f : Func n) (g : Nat) : Prop :=
  ∃ m t, IsOpt f m ∧ IsTree f t ∧ t = m + g

theorem fanOut_nil (n p : Nat) : fanOut n [] p = 0 := rfl

theorem numReconv_nil (n : Nat) : numReconv n [] = 0 := rfl

theorem fanOut_le_length (n : Nat) (gs : List Gate) (p : Nat) :
    fanOut n gs p ≤ gs.length :=
  List.countP_le_length

theorem numReconv_le_length (n : Nat) (gs : List Gate) :
    numReconv n gs ≤ gs.length := by
  have h : numReconv n gs ≤ (List.range gs.length).length := List.countP_le_length
  simpa [List.length_range] using h

theorem fanOut_last_eq_zero (n : Nat) (gs : List Gate) (hwf : wfC n gs) :
    fanOut n gs (gs.length - 1) = 0 := by
  rw [fanOut, List.countP_eq_zero]
  intro g hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hw : (gs[i]).ia < n + i ∧ (gs[i]).ib < n + i := by
    have h := hwf ⟨i, hi⟩
    simpa [List.get_eq_getElem] using h
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq, not_or]
  omega

theorem numReconv_singleton (n : Nat) (g : Gate) (hwf : wfC n [g]) :
    numReconv n [g] = 0 := by
  have h := fanOut_last_eq_zero n [g] hwf
  simp only [List.length_singleton] at h
  simp [numReconv, h]

theorem ctrl_wf : wfC 2 [⟨false, 0, false, 1⟩, ⟨false, 2, true, 2⟩] := by
  intro p
  obtain ⟨i, hi⟩ := p
  simp only [List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by simp, by simp⟩
  | 1, _ => exact ⟨by simp, by simp⟩
  | (k + 2), h => exact absurd h (by omega)

theorem sharing_defs_differ :
    fanOut 2 [⟨false, 0, false, 1⟩, ⟨false, 2, true, 2⟩] 0 = 1 ∧
    fanOutEdges 2 [⟨false, 0, false, 1⟩, ⟨false, 2, true, 2⟩] 0 = 2 := by
  refine ⟨by decide, by decide⟩

theorem ctrl_numReconv : numReconv 2 [⟨false, 0, false, 1⟩, ⟨false, 2, true, 2⟩] = 0 := by
  decide

theorem shared_wf :
    wfC 2 [⟨false, 0, false, 1⟩, ⟨false, 2, false, 0⟩, ⟨false, 2, false, 1⟩] := by
  intro p
  obtain ⟨i, hi⟩ := p
  simp only [List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by simp, by simp⟩
  | 1, _ => exact ⟨by simp, by simp⟩
  | 2, _ => exact ⟨by simp, by simp⟩
  | (k + 3), h => exact absurd h (by omega)

theorem shared_is_detected :
    fanOut 2 [⟨false, 0, false, 1⟩, ⟨false, 2, false, 0⟩, ⟨false, 2, false, 1⟩] 0 = 2 ∧
    numReconv 2 [⟨false, 0, false, 1⟩, ⟨false, 2, false, 0⟩, ⟨false, 2, false, 1⟩] = 1 := by
  refine ⟨by decide, by decide⟩

theorem chain_no_sharing :
    numReconv 2 [⟨false, 0, false, 1⟩, ⟨false, 2, false, 0⟩] = 0 := by
  decide

#print axioms fanOut_le_length
#print axioms numReconv_le_length
#print axioms fanOut_last_eq_zero
#print axioms numReconv_singleton
#print axioms ctrl_wf
#print axioms sharing_defs_differ
#print axioms ctrl_numReconv
#print axioms shared_wf
#print axioms shared_is_detected
#print axioms chain_no_sharing

def dropLast (x : Assign (n + 1)) : Assign n := fun i => x i.castSucc

def liftAnd (z : Func n) : Func (n + 1) := fun x => z (dropLast x) && x (Fin.last n)

def liftOr (z : Func n) : Func (n + 1) := fun x => z (dropLast x) || x (Fin.last n)

def shiftFrm : Frm n → Frm (n + 1)
  | .var i => .var i.castSucc
  | .one => .one
  | .and pa a pb b => .and pa (shiftFrm a) pb (shiftFrm b)

theorem evalF_shiftFrm (φ : Frm n) (x : Assign (n + 1)) :
    evalF (shiftFrm φ) x = evalF φ (dropLast x) := by
  induction φ with
  | var i => rfl
  | one => rfl
  | and pa a pb b iha ihb => simp [shiftFrm, evalF, iha, ihb]

theorem gatesF_shiftFrm (φ : Frm n) : gatesF (shiftFrm φ) = gatesF φ := by
  induction φ with
  | var i => rfl
  | one => rfl
  | and pa a pb b iha ihb => simp [shiftFrm, gatesF, iha, ihb]

def liftFrm (pa : Bool) (φ : Frm n) : Frm (n + 1) :=
  .and pa (shiftFrm φ) false (.var (Fin.last n))

theorem gatesF_liftFrm (pa : Bool) (φ : Frm n) :
    gatesF (liftFrm pa φ) = gatesF φ + 1 := by
  simp [liftFrm, gatesF, gatesF_shiftFrm]
  omega

theorem hasFormula_liftAnd (z : Func n) (k : Nat) (h : HasFormula z k) :
    HasFormula (liftAnd z) (k + 1) := by
  obtain ⟨φ, hk, hc⟩ := h
  rcases hc with hc | hc
  · refine ⟨liftFrm false φ, by simp [gatesF_liftFrm]; omega, Or.inl ?_⟩
    funext x
    simp [liftFrm, evalF, evalF_shiftFrm, hc, liftAnd, Fin.last]
  · refine ⟨liftFrm true φ, by simp [gatesF_liftFrm]; omega, Or.inl ?_⟩
    funext x
    have : evalF φ (dropLast x) = !(z (dropLast x)) := by rw [hc]
    simp [liftFrm, evalF, evalF_shiftFrm, this, liftAnd, Fin.last]

def shiftWire (n w : Nat) : Nat := if w < n then w else w + 1

def shiftGate (n : Nat) (g : Gate) : Gate :=
  ⟨g.na, shiftWire n g.ia, g.nb, shiftWire n g.ib⟩

def gstep (x : Assign n) (vals : Array Bool) (g : Gate) : Array Bool :=
  vals.push ((xor g.na (wireVal x vals g.ia)) && (xor g.nb (wireVal x vals g.ib)))

theorem evalGates_foldl (x : Assign n) (gs : List Gate) :
    evalGates x gs = gs.foldl (gstep x) #[] := rfl

theorem wireVal_shift (n : Nat) (x : Assign (n + 1)) (vals : Array Bool) (w : Nat) :
    wireVal x vals (shiftWire n w) = wireVal (dropLast x) vals w := by
  unfold shiftWire wireVal
  by_cases h : w < n
  · have h2 : w < n + 1 := by omega
    simp [h, h2, dropLast, Fin.castSucc, Fin.castAdd, Fin.castLE]
  · have h1 : ¬ (w + 1 < n + 1) := by omega
    simp [h, h1]

theorem foldl_shift (n : Nat) (x : Assign (n + 1)) (gs : List Gate) :
    ∀ acc : Array Bool,
      (gs.map (shiftGate n)).foldl (gstep x) acc = gs.foldl (gstep (dropLast x)) acc := by
  induction gs with
  | nil => intro acc; rfl
  | cons g t ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      have hstep : gstep x acc (shiftGate n g) = gstep (dropLast x) acc g := by
        simp [gstep, shiftGate, wireVal_shift]
      rw [hstep, ih]

theorem size_foldl (x : Assign n) (gs : List Gate) :
    ∀ acc : Array Bool, (gs.foldl (gstep x) acc).size = acc.size + gs.length := by
  induction gs with
  | nil => intro acc; simp
  | cons g t ih =>
      intro acc
      simp only [List.foldl_cons, ih, gstep, Array.size_push, List.length_cons]
      omega

theorem size_evalGates (x : Assign n) (gs : List Gate) :
    (evalGates x gs).size = gs.length := by
  rw [evalGates_foldl, size_foldl]
  simp

def liftCircuit (n : Nat) (na : Bool) (gs : List Gate) : List Gate :=
  gs.map (shiftGate n) ++ [⟨na, (n + 1) + (gs.length - 1), false, n⟩]

theorem length_liftCircuit (n : Nat) (na : Bool) (gs : List Gate) :
    (liftCircuit n na gs).length = gs.length + 1 := by
  simp [liftCircuit]

theorem circuitOut_liftCircuit (n : Nat) (na : Bool) (x : Assign (n + 1)) (gs : List Gate) :
    circuitOut x (liftCircuit n na gs)
      = ((xor na (circuitOut (dropLast x) gs)) && x (Fin.last n)) := by
  have hA : (evalGates (dropLast x) gs).size = gs.length := size_evalGates _ _
  have hfold : evalGates x (liftCircuit n na gs)
      = gstep x (evalGates (dropLast x) gs) ⟨na, (n + 1) + (gs.length - 1), false, n⟩ := by
    rw [evalGates_foldl, liftCircuit, List.foldl_append, foldl_shift]
    rw [evalGates_foldl]
    simp [List.foldl_cons]
  have hlast : wireVal x (evalGates (dropLast x) gs) n = x (Fin.last n) := by
    unfold wireVal
    simp [Fin.last]
  have hout : wireVal x (evalGates (dropLast x) gs) ((n + 1) + (gs.length - 1))
      = circuitOut (dropLast x) gs := by
    unfold wireVal circuitOut
    have h1 : ¬ ((n + 1) + (gs.length - 1) < n + 1) := by omega
    have harith : (n + 1) + (gs.length - 1) - (n + 1) = gs.length - 1 := by omega
    simp only [h1, harith]
    simp
  rw [circuitOut, hfold, gstep, hlast, hout, length_liftCircuit, Nat.add_sub_cancel, ← hA]
  simp

theorem const_of_nil (z : Func n) (h : CircuitComputes ([] : List Gate) z) :
    z = (fun _ => false) ∨ z = (fun _ => true) := by
  have hout : ∀ x : Assign n, circuitOut x ([] : List Gate) = false := by
    intro x; rfl
  rcases h with h | h
  · left
    funext x
    have := h x
    rw [hout x] at this
    exact this.symm
  · right
    funext x
    have := h x
    rw [hout x] at this
    cases hb : z x
    · simp [hb] at this
    · rfl

theorem wfC_liftCircuit (n : Nat) (na : Bool) (gs : List Gate)
    (h : wfC n gs) (hne : 0 < gs.length) :
    wfC (n + 1) (liftCircuit n na gs) := by
  intro p
  obtain ⟨i, hi⟩ := p
  rw [List.get_eq_getElem]
  rw [length_liftCircuit] at hi
  by_cases hlt : i < gs.length
  · have hidx : (liftCircuit n na gs)[i] = shiftGate n gs[i] := by
      simp [liftCircuit, List.getElem_append_left, hlt]
    have hw : gs[i].ia < n + i ∧ gs[i].ib < n + i := by
      have hh := h ⟨i, hlt⟩
      simpa [List.get_eq_getElem] using hh
    rw [hidx]
    simp only [shiftGate, shiftWire]
    refine ⟨?_, ?_⟩ <;> split <;> omega
  · have hieq : i = gs.length := by omega
    subst hieq
    have hidx : (liftCircuit n na gs)[gs.length]
        = (⟨na, (n + 1) + (gs.length - 1), false, n⟩ : Gate) := by
      simp [liftCircuit]
    rw [hidx]
    refine ⟨?_, ?_⟩
    · show (n + 1) + (gs.length - 1) < n + 1 + gs.length
      omega
    · show n < n + 1 + gs.length
      omega

theorem hasCircuit_liftAnd (z : Func n) (k : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (h : HasCircuit z k) :
    HasCircuit (liftAnd z) (k + 1) := by
  obtain ⟨gs, hwf, hlen, hc⟩ := h
  have hne : 0 < gs.length := by
    rcases Nat.eq_zero_or_pos gs.length with h0 | hpos
    · exfalso
      have : gs = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      rcases const_of_nil z hc with hk | hk
      · exact hz0 hk
      · exact hz1 hk
    · exact hpos

  rcases hc with hc | hc
  · refine ⟨liftCircuit n false gs, wfC_liftCircuit n false gs hwf hne, ?_, Or.inl ?_⟩
    · rw [length_liftCircuit]; omega
    · intro x
      rw [circuitOut_liftCircuit, hc]
      simp [liftAnd]
  · refine ⟨liftCircuit n true gs, wfC_liftCircuit n true gs hwf hne, ?_, Or.inl ?_⟩
    · rw [length_liftCircuit]; omega
    · intro x
      rw [circuitOut_liftCircuit, hc]
      simp [liftAnd]

theorem lift_control :
    (∀ x : Assign 3, liftAnd (fun y : Assign 2 => y 0) x = (x 0 && x 2)) ∧
    (∀ x : Assign 3, liftOr (fun y : Assign 2 => y 0) x = (x 0 || x 2)) := by
  refine ⟨?_, ?_⟩ <;> intro x <;> rfl

theorem lift_upper_bounds (z : Func n) (mz tz : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (hopt : IsOpt z mz) (htree : IsTree z tz) :
    HasCircuit (liftAnd z) (mz + 1) ∧ HasFormula (liftAnd z) (tz + 1) :=
  ⟨hasCircuit_liftAnd z mz hz0 hz1 hopt.1, hasFormula_liftAnd z tz htree.1⟩

#print axioms evalF_shiftFrm
#print axioms hasFormula_liftAnd
#print axioms circuitOut_liftCircuit
#print axioms wfC_liftCircuit
#print axioms const_of_nil
#print axioms hasCircuit_liftAnd
#print axioms lift_control
#print axioms lift_upper_bounds

def contractWire (n p a w : Nat) : Nat :=
  if w = n + p then a else if n + p < w then w - 1 else w

def contractGate (n p a : Nat) (inv : Bool) (g : Gate) : Gate :=
  ⟨xor g.na (decide (g.ia = n + p) && inv), contractWire n p a g.ia,
   xor g.nb (decide (g.ib = n + p) && inv), contractWire n p a g.ib⟩

def contract (n p a : Nat) (inv : Bool) (gs : List Gate) : List Gate :=
  (gs.eraseIdx p).map (contractGate n p a inv)

theorem length_contract (n p a : Nat) (inv : Bool) (gs : List Gate) (hp : p < gs.length) :
    (contract n p a inv gs).length = gs.length - 1 := by
  simp [contract, List.length_eraseIdx, hp]

def oldIdx (p q : Nat) : Nat := if q < p then q else q + 1

def IsPassThroughAt (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool) : Prop :=
  ∀ x : Assign n,
    (evalGates x gs).getD p false = xor inv (wireVal x (evalGates x gs) a)

def IsPassThrough (n : Nat) (gs : List Gate) (p a : Nat) : Prop :=
  ∃ inv : Bool, IsPassThroughAt n gs p a inv

private theorem getD_push_ne (v : Array Bool) (b : Bool) (j : Nat) (h : j ≠ v.size) :
    (v.push b).getD j false = v.getD j false := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h]

private theorem getD_push_self (v : Array Bool) (b : Bool) :
    (v.push b).getD v.size false = b := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]

private theorem getD_foldl_lt {n : Nat} (x : Assign n) :
    ∀ (l : List Gate) (acc : Array Bool) (j : Nat), j < acc.size →
      (l.foldl (gstep x) acc).getD j false = acc.getD j false
  | [], _, _, _ => rfl
  | g :: t, acc, j, h => by
      rw [List.foldl_cons]
      have hs : (gstep x acc g).size = acc.size + 1 := by simp [gstep]
      rw [getD_foldl_lt x t _ j (by omega)]
      exact getD_push_ne acc _ j (by omega)

private theorem wireVal_foldl {n : Nat} (x : Assign n) (l : List Gate) (acc : Array Bool) (w : Nat)
    (h : w < n ∨ w - n < acc.size) :
    wireVal x (l.foldl (gstep x) acc) w = wireVal x acc w := by
  unfold wireVal
  split
  · rfl
  · exact getD_foldl_lt x l acc (w - n) (by omega)

private theorem contractGate_id (n p a : Nat) (inv : Bool) (g : Gate)
    (h1 : g.ia < n + p) (h2 : g.ib < n + p) : contractGate n p a inv g = g := by
  unfold contractGate contractWire
  simp [show g.ia ≠ n + p by omega, show ¬ (n + p < g.ia) by omega,
        show g.ib ≠ n + p by omega, show ¬ (n + p < g.ib) by omega]

private theorem map_contractGate_id (n p a : Nat) (inv : Bool) :
    ∀ l : List Gate, (∀ g ∈ l, g.ia < n + p ∧ g.ib < n + p) →
      l.map (contractGate n p a inv) = l
  | [], _ => rfl
  | g :: t, h => by
      have hg := h g (by simp)
      rw [List.map_cons, contractGate_id n p a inv g hg.1 hg.2,
          map_contractGate_id n p a inv t (fun y hy => h y (by simp [hy]))]

private theorem wf_take (n : Nat) (gs : List Gate) (p : Nat) (hwf : wfC n gs) :
    ∀ g ∈ gs.take p, g.ia < n + p ∧ g.ib < n + p := by
  intro g hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hlen : (gs.take p).length = min p gs.length := List.length_take
  have hip : i < p := by omega
  have hig : i < gs.length := by omega
  have hw := hwf ⟨i, hig⟩
  simp only [List.get_eq_getElem] at hw
  rw [List.getElem_take]
  exact ⟨by omega, by omega⟩

private def Corr (p k : Nat) (V W : Array Bool) : Prop :=
  V.size = k ∧ W.size = k + 1 ∧
  (∀ j, j < p → V.getD j false = W.getD j false) ∧
  (∀ j, p ≤ j → j < k → V.getD j false = W.getD (j + 1) false)

private theorem wireVal_ge {n : Nat} (x : Assign n) (V : Array Bool) (w : Nat) (h : ¬ w < n) :
    wireVal x V w = V.getD (w - n) false := by
  unfold wireVal; simp [h]

private theorem wireVal_lt {n : Nat} (x : Assign n) (V : Array Bool) (w : Nat) (h : w < n) :
    wireVal x V w = x ⟨w, h⟩ := by
  unfold wireVal; simp [h]

private theorem wire_corr {n : Nat} (x : Assign n) (p a : Nat) (inv : Bool) (ha : a < n + p)
    (V W : Array Bool) (k : Nat) (hc : Corr p k V W) (hp : p ≤ k)
    (hpt : W.getD p false = xor inv (wireVal x W a))
    (w : Nat) (hw : w < n + k + 1) :
    xor (decide (w = n + p) && inv) (wireVal x V (contractWire n p a w)) = wireVal x W w := by
  obtain ⟨hV, hW, hlo, hhi⟩ := hc
  have hVa : wireVal x V a = wireVal x W a := by
    by_cases han : a < n
    · rw [wireVal_lt x V a han, wireVal_lt x W a han]
    · rw [wireVal_ge x V a han, wireVal_ge x W a han]
      exact hlo (a - n) (by omega)
  by_cases hn : w < n
  · have hcw : contractWire n p a w = w := by
      unfold contractWire; simp [show w ≠ n + p by omega, show ¬ (n + p < w) by omega]
    rw [hcw, wireVal_lt x V w hn, wireVal_lt x W w hn]
    simp [show w ≠ n + p by omega]
  · by_cases heq : w = n + p
    · have hcw : contractWire n p a w = a := by unfold contractWire; simp [heq]
      rw [hcw, hVa, wireVal_ge x W w hn]
      have hwp : w - n = p := by omega
      rw [hwp, hpt]
      simp [heq]
    · by_cases hlt : w < n + p
      · have hcw : contractWire n p a w = w := by
          unfold contractWire; simp [heq, show ¬ (n + p < w) by omega]
        rw [hcw, wireVal_ge x V w hn, wireVal_ge x W w hn]
        rw [hlo (w - n) (by omega)]
        simp [heq]
      · have hgt : n + p < w := by omega
        have hcw : contractWire n p a w = w - 1 := by
          unfold contractWire; simp [heq, hgt]
        have hn1 : ¬ (w - 1 < n) := by omega
        rw [hcw, wireVal_ge x V (w - 1) hn1, wireVal_ge x W w hn]
        rw [hhi (w - 1 - n) (by omega) (by omega)]
        have he : w - 1 - n + 1 = w - n := by omega
        rw [he]
        simp [heq]

private theorem corr_step {n : Nat} (x : Assign n) (p a : Nat) (inv : Bool) (ha : a < n + p)
    (V W : Array Bool) (k : Nat) (hc : Corr p k V W) (hp : p ≤ k)
    (hpt : W.getD p false = xor inv (wireVal x W a))
    (g : Gate) (h1 : g.ia < n + k + 1) (h2 : g.ib < n + k + 1) :
    Corr p (k + 1) (gstep x V (contractGate n p a inv g)) (gstep x W g) := by
  have hva := wire_corr x p a inv ha V W k hc hp hpt g.ia h1
  have hvb := wire_corr x p a inv ha V W k hc hp hpt g.ib h2
  obtain ⟨hV, hW, hlo, hhi⟩ := hc
  have hval : ((xor (xor g.na (decide (g.ia = n + p) && inv))
                   (wireVal x V (contractWire n p a g.ia)))
              && (xor (xor g.nb (decide (g.ib = n + p) && inv))
                   (wireVal x V (contractWire n p a g.ib))))
            = ((xor g.na (wireVal x W g.ia)) && (xor g.nb (wireVal x W g.ib))) := by
    rw [Bool.xor_assoc, Bool.xor_assoc, hva, hvb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold gstep; simp [hV]
  · unfold gstep; simp [hW]
  · intro j hj
    unfold gstep
    rw [getD_push_ne V _ j (by omega), getD_push_ne W _ j (by omega)]
    exact hlo j hj
  · intro j hjp hjk
    by_cases hjs : j = k
    · rw [hjs, ← hW, ← hV]
      unfold gstep
      rw [getD_push_self V _, getD_push_self W _]
      exact hval
    · unfold gstep
      rw [getD_push_ne V _ j (by omega), getD_push_ne W _ (j + 1) (by omega)]
      exact hhi j hjp (by omega)

private theorem corr_foldl {n : Nat} (x : Assign n) (p a : Nat) (inv : Bool) (ha : a < n + p) :
    ∀ (post : List Gate) (V W : Array Bool) (k : Nat), Corr p k V W → p ≤ k →
      W.getD p false = xor inv (wireVal x W a) →
      (∀ (i : Nat) (hi : i < post.length),
          post[i].ia < n + k + 1 + i ∧ post[i].ib < n + k + 1 + i) →
      Corr p (k + post.length) ((post.map (contractGate n p a inv)).foldl (gstep x) V)
                               (post.foldl (gstep x) W)
  | [], V, W, k, hc, _, _, _ => by simpa using hc
  | g :: t, V, W, k, hc, hp, hpt, hb => by
      have hg := hb 0 (by simp)
      simp only [List.getElem_cons_zero] at hg
      have hstep := corr_step x p a inv ha V W k hc hp hpt g (by omega) (by omega)
      have hpt' : (gstep x W g).getD p false = xor inv (wireVal x (gstep x W g) a) := by
        obtain ⟨hV, hW, _, _⟩ := hc
        unfold gstep
        rw [getD_push_ne W _ p (by omega)]
        have e2 : wireVal x (W.push ((xor g.na (wireVal x W g.ia))
              && (xor g.nb (wireVal x W g.ib)))) a = wireVal x W a := by
          by_cases han : a < n
          · rw [wireVal_lt x _ a han, wireVal_lt x W a han]
          · rw [wireVal_ge x _ a han, wireVal_ge x W a han]
            exact getD_push_ne W _ (a - n) (by omega)
        rw [e2, hpt]
      have hb' : ∀ (i : Nat) (hi : i < t.length),
          t[i].ia < n + (k + 1) + 1 + i ∧ t[i].ib < n + (k + 1) + 1 + i := by
        intro i hi
        have hbi := hb (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at hbi
        exact ⟨by omega, by omega⟩
      have hrec := corr_foldl x p a inv ha t (gstep x V (contractGate n p a inv g))
        (gstep x W g) (k + 1) hstep (by omega) hpt' hb'
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      have e : k + 1 + t.length = k + (t.length + 1) := by omega
      rw [← e]
      exact hrec

theorem evalGates_contract (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hp : p < gs.length) (ha : a < n + p) (x : Assign n)
    (hpt : (evalGates x gs).getD p false = xor inv (wireVal x (evalGates x gs) a)) :
    ∀ q, q < gs.length - 1 →
      (evalGates x (contract n p a inv gs)).getD q false
        = (evalGates x gs).getD (oldIdx p q) false := by
  have hdec : gs.take p ++ gs[p] :: gs.drop (p + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have hpre : (gs.take p).map (contractGate n p a inv) = gs.take p :=
    map_contractGate_id n p a inv _ (wf_take n gs p hwf)
  have hgs' : contract n p a inv gs
      = gs.take p ++ (gs.drop (p + 1)).map (contractGate n p a inv) := by
    rw [contract, List.eraseIdx_eq_take_drop_succ, List.map_append, hpre]
  have hPsize : (evalGates x (gs.take p)).size = p := by
    rw [size_evalGates, List.length_take]; omega
  have key : ∀ l : List Gate, l = gs.take p ++ gs[p] :: gs.drop (p + 1) →
      evalGates x l = (gs.drop (p + 1)).foldl (gstep x)
        (gstep x (evalGates x (gs.take p)) gs[p]) := by
    intro l hl
    rw [hl, evalGates_foldl, List.foldl_append, List.foldl_cons, evalGates_foldl]
  have key2 : ∀ l : List Gate, l = gs.take p ++ (gs.drop (p + 1)).map (contractGate n p a inv) →
      evalGates x l = ((gs.drop (p + 1)).map (contractGate n p a inv)).foldl (gstep x)
        (evalGates x (gs.take p)) := by
    intro l hl
    rw [hl, evalGates_foldl, List.foldl_append, evalGates_foldl]
  have hEgs := key gs hdec.symm
  have hEgs' := key2 _ hgs'
  have hWs : (gstep x (evalGates x (gs.take p)) gs[p]).size = p + 1 := by
    unfold gstep; simp [hPsize]
  have hCorr0 : Corr p p (evalGates x (gs.take p))
      (gstep x (evalGates x (gs.take p)) gs[p]) := by
    refine ⟨hPsize, hWs, ?_, ?_⟩
    · intro j hj
      unfold gstep
      exact (getD_push_ne _ _ j (by omega)).symm
    · intro j h1 h2
      exact absurd h2 (by omega)
  have hptW : (gstep x (evalGates x (gs.take p)) gs[p]).getD p false
      = xor inv (wireVal x (gstep x (evalGates x (gs.take p)) gs[p]) a) := by
    have hA := hpt
    rw [hEgs] at hA
    rw [getD_foldl_lt x _ _ p (by omega)] at hA
    rw [wireVal_foldl x _ _ a (by omega)] at hA
    exact hA
  have hLd : (gs.drop (p + 1)).length = gs.length - (p + 1) := List.length_drop
  have hbounds : ∀ (i : Nat) (hi : i < (gs.drop (p + 1)).length),
      (gs.drop (p + 1))[i].ia < n + p + 1 + i ∧ (gs.drop (p + 1))[i].ib < n + p + 1 + i := by
    intro i hi
    have hig : p + 1 + i < gs.length := by omega
    have hw := hwf ⟨p + 1 + i, hig⟩
    simp only [List.get_eq_getElem] at hw
    rw [List.getElem_drop]
    exact ⟨by omega, by omega⟩
  have hfin := corr_foldl x p a inv ha (gs.drop (p + 1)) (evalGates x (gs.take p))
    (gstep x (evalGates x (gs.take p)) gs[p]) p hCorr0 (Nat.le_refl p) hptW hbounds
  obtain ⟨_, _, hlo, hhi⟩ := hfin
  intro q hq
  rw [hEgs, hEgs']
  by_cases hqp : q < p
  · have ho : oldIdx p q = q := by unfold oldIdx; simp [hqp]
    rw [ho]; exact hlo q hqp
  · have ho : oldIdx p q = q + 1 := by unfold oldIdx; simp [hqp]
    rw [ho]
    exact hhi q (by omega) (by omega)

theorem circuitOut_contract_at (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hp : p + 1 < gs.length) (ha : a < n + p) (x : Assign n)
    (hpt : (evalGates x gs).getD p false = xor inv (wireVal x (evalGates x gs) a)) :
    circuitOut x (contract n p a inv gs) = circuitOut x gs := by
  have hp' : p < gs.length := by omega
  unfold circuitOut
  rw [length_contract n p a inv gs hp']
  rw [evalGates_contract n gs p a inv hwf hp' ha x hpt _ (by omega)]
  have ho : oldIdx p (gs.length - 1 - 1) = gs.length - 1 := by
    unfold oldIdx
    rw [if_neg (show ¬ (gs.length - 1 - 1 < p) from by omega)]
    omega
  rw [ho]

theorem circuitOut_contract (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hp : p + 1 < gs.length) (ha : a < n + p)
    (hpt : IsPassThroughAt n gs p a inv)
    (f : Func n) (hc : CircuitComputes gs f) :
    CircuitComputes (contract n p a inv gs) f := by
  rcases hc with h | h
  · exact Or.inl (fun x => by
      rw [circuitOut_contract_at n gs p a inv hwf hp ha x (hpt x)]; exact h x)
  · exact Or.inr (fun x => by
      rw [circuitOut_contract_at n gs p a inv hwf hp ha x (hpt x)]; exact h x)

theorem circuitOut_contract_output_at (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hlast : p + 1 = gs.length) (h2 : 2 ≤ gs.length)
    (ha : a = n + (gs.length - 2)) (x : Assign n)
    (hpt : (evalGates x gs).getD p false = xor inv (wireVal x (evalGates x gs) a)) :
    circuitOut x (contract n p a inv gs) = xor inv (circuitOut x gs) := by
  have hp' : p < gs.length := by omega
  have halt : a < n + p := by omega
  have eL : (evalGates x gs).getD (gs.length - 1) false
      = xor inv ((evalGates x gs).getD (gs.length - 2) false) := by
    have e1 : (evalGates x gs).getD (gs.length - 1) false
        = (evalGates x gs).getD p false := by
      rw [show gs.length - 1 = p from by omega]
    rw [e1, hpt, wireVal_ge x (evalGates x gs) a (by omega),
        show a - n = gs.length - 2 from by omega]
  have eR : (evalGates x (contract n p a inv gs)).getD (gs.length - 2) false
      = (evalGates x gs).getD (gs.length - 2) false := by
    rw [evalGates_contract n gs p a inv hwf hp' halt x hpt _ (by omega),
        show oldIdx p (gs.length - 2) = gs.length - 2 from by
          unfold oldIdx; rw [if_pos (show gs.length - 2 < p from by omega)]]
  unfold circuitOut
  rw [length_contract n p a inv gs hp', show gs.length - 1 - 1 = gs.length - 2 from by omega,
      eR, eL]
  cases inv <;> simp

theorem circuitOut_contract_output (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hlast : p + 1 = gs.length) (h2 : 2 ≤ gs.length)
    (ha : a = n + (gs.length - 2))
    (hpt : IsPassThroughAt n gs p a inv)
    (f : Func n) (hc : CircuitComputes gs f) :
    CircuitComputes (contract n p a inv gs) f := by
  have hout : ∀ x : Assign n,
      circuitOut x (contract n p a inv gs) = xor inv (circuitOut x gs) :=
    fun x => circuitOut_contract_output_at n gs p a inv hwf hlast h2 ha x (hpt x)
  rcases hc with h | h
  · cases inv with
    | false => exact Or.inl (fun x => by rw [hout x, h x]; simp)
    | true => exact Or.inr (fun x => by rw [hout x, h x]; simp)
  · cases inv with
    | false => exact Or.inr (fun x => by rw [hout x, h x]; simp)
    | true => exact Or.inl (fun x => by rw [hout x, h x]; simp)

private def noGs : List Gate := [⟨false, 0, false, 0⟩, ⟨false, 1, false, 1⟩]
private def noF : Func 2 := fun x => x 1
private def noX_TF : Assign 2 := fun j => if j.val = 0 then true else false
private def noX_FF : Assign 2 := fun _ => false

theorem contract_needs_nonoutput :
    wfC 2 noGs ∧ (1 : Nat) < noGs.length ∧ IsPassThroughAt 2 noGs 1 1 false
      ∧ CircuitComputes noGs noF
      ∧ ¬ CircuitComputes (contract 2 1 1 false noGs) noF := by
  refine ⟨?_, by decide, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨i, hi⟩ := q
    simp only [noGs, List.length_cons, List.length_nil] at hi
    match i, hi with
    | 0, _ => exact ⟨by show (0:Nat) < 2; decide, by show (0:Nat) < 2; decide⟩
    | 1, _ => exact ⟨by show (1:Nat) < 3; decide, by show (1:Nat) < 3; decide⟩
    | (k + 2), h => exact absurd h (by omega)
  · intro x
    simp [noGs, evalGates, wireVal]
  · refine Or.inl ?_
    intro x
    simp [noGs, noF, circuitOut, evalGates, wireVal]
  · rintro (h | h)
    · have hx := h noX_TF
      simp [noGs, noF, noX_TF, contract, contractGate, contractWire, circuitOut, evalGates,
        wireVal] at hx
    · have hx := h noX_FF
      simp [noGs, noF, noX_FF, contract, contractGate, contractWire, circuitOut, evalGates,
        wireVal] at hx

#print axioms evalGates_contract
#print axioms circuitOut_contract
#print axioms circuitOut_contract_output
#print axioms contract_needs_nonoutput

private theorem countP_or_le {α : Type} (f g : α → Bool) :
    ∀ l : List α, l.countP (fun x => f x || g x) ≤ l.countP f + l.countP g
  | [] => by simp
  | x :: t => by
      have ih := countP_or_le f g t
      simp only [List.countP_cons]
      by_cases hf : f x = true <;> by_cases hg : g x = true <;>
        simp [hf, hg] <;> omega

private theorem countP_eraseIdx_succ_le {α : Type} (f : α → Bool) :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), f (l.get ⟨i, hi⟩) = true →
      (l.eraseIdx i).countP f + 1 ≤ l.countP f
  | [], i, hi, _ => absurd hi (by simp)
  | x :: t, 0, _, hx => by
      simp only [List.get] at hx
      simp [List.eraseIdx, hx]
  | x :: t, (i + 1), hi, hx => by
      simp only [List.length_cons] at hi
      have hi' : i < t.length := by omega
      have hx' : f (t.get ⟨i, hi'⟩) = true := by simpa [List.get] using hx
      have ih := countP_eraseIdx_succ_le f t i hi' hx'
      simp only [List.eraseIdx, List.countP_cons]
      by_cases h : f x = true <;> simp [h] <;> omega

private theorem countP_mono_except (f g : Nat → Bool) (c : Nat) :
    ∀ l : List Nat, (∀ x ∈ l, x ≠ c → f x = true → g x = true) →
      l.countP f ≤ l.countP g + l.countP (fun x => decide (x = c))
  | [], _ => by simp
  | x :: t, h => by
      have ih := countP_mono_except f g c t (fun y hy => h y (by simp [hy]))
      simp only [List.countP_cons]
      by_cases hxc : x = c
      · subst hxc
        by_cases hf : f x = true <;> by_cases hg : g x = true <;>
          simp [hf, hg] <;> omega
      · have hxg := h x (by simp) hxc
        by_cases hf : f x = true
        · have hg := hxg hf
          simp [hf, hg, hxc] <;> omega
        · simp [hf, hxc] <;> omega

private theorem countP_eq_range (c : Nat) :
    ∀ p : Nat, (List.range p).countP (fun x => decide (x = c)) = if c < p then 1 else 0
  | 0 => by simp
  | (p + 1) => by
      have ih := countP_eq_range c p
      rw [List.range_succ, List.countP_append, ih]
      by_cases h1 : c < p
      · simp [h1, show p ≠ c by omega, Nat.lt_succ_of_lt h1]
      · by_cases h2 : c = p
        · subst h2; simp [h1]
        · simp [h1, show ¬ (c < p + 1) by omega, show ¬ p = c by omega]

private theorem countP_range_split (f : Nat → Bool) (p m : Nat) :
    (List.range (p + m)).countP f
      = (List.range p).countP f + (List.range m).countP (fun j => f (p + j)) := by
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

private theorem contractWire_inv (n p a w q : Nat) (hqa : n + q ≠ a)
    (h : contractWire n p a w = n + q) : w = n + oldIdx p q := by
  unfold contractWire at h
  by_cases h1 : w = n + p
  · rw [if_pos h1] at h; exact absurd h.symm hqa
  · rw [if_neg h1] at h
    by_cases h2 : n + p < w
    · rw [if_pos h2] at h; unfold oldIdx; split <;> omega
    · rw [if_neg h2] at h; unfold oldIdx; split <;> omega

private theorem contractWire_inv_a (n p a w : Nat) (hlt : a < n + p)
    (h : contractWire n p a w = a) : w = a ∨ w = n + p := by
  unfold contractWire at h
  by_cases h1 : w = n + p
  · exact Or.inr h1
  · rw [if_neg h1] at h
    by_cases h2 : n + p < w
    · rw [if_pos h2] at h; omega
    · rw [if_neg h2] at h; exact Or.inl h

private theorem refsWire_contract_inv (n p a q : Nat) (inv : Bool) (g : Gate) (hqa : n + q ≠ a)
    (h : refsWire (contractGate n p a inv g) (n + q) = true) :
    refsWire g (n + oldIdx p q) = true := by
  simp only [refsWire, contractGate, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | h
  · exact Or.inl (contractWire_inv n p a _ q hqa h)
  · exact Or.inr (contractWire_inv n p a _ q hqa h)

private theorem refsWire_contract_inv_a (n p a : Nat) (inv : Bool) (g : Gate) (hlt : a < n + p)
    (h : refsWire (contractGate n p a inv g) a = true) :
    (refsWire g a || refsWire g (n + p)) = true := by
  simp only [refsWire, contractGate, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | h
  · rcases contractWire_inv_a n p a _ hlt h with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inr (Or.inl h')
  · rcases contractWire_inv_a n p a _ hlt h with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr (Or.inr h')

private theorem fanOut_contract_le (n : Nat) (gs : List Gate) (p a q : Nat) (inv : Bool)
    (hqa : n + q ≠ a) :
    fanOut n (contract n p a inv gs) q ≤ fanOut n gs (oldIdx p q) := by
  simp only [fanOut, contract, List.countP_map, Function.comp_def]
  refine Nat.le_trans (List.countP_mono_left
    (fun g _ h => refsWire_contract_inv n p a q inv g hqa h)) ?_
  exact (List.eraseIdx_sublist gs p).countP_le

private theorem fanOut_contract_a_le (n : Nat) (gs : List Gate) (p a q : Nat) (inv : Bool)
    (hlt : a < n + p) (hqa : n + q = a) (hp : p < gs.length)
    (href : refsWire (gs.get ⟨p, hp⟩) a = true) :
    fanOut n (contract n p a inv gs) q + 1 ≤ fanOut n gs q + fanOut n gs p := by
  have h1 : fanOut n (contract n p a inv gs) q
      ≤ (gs.eraseIdx p).countP (fun g => refsWire g a)
        + (gs.eraseIdx p).countP (fun g => refsWire g (n + p)) := by
    simp only [fanOut, contract, List.countP_map, Function.comp_def, hqa]
    refine Nat.le_trans (List.countP_mono_left
      (fun g _ h => refsWire_contract_inv_a n p a inv g hlt h)) ?_
    exact countP_or_le _ _ _
  have h2 : (gs.eraseIdx p).countP (fun g => refsWire g a) + 1
      ≤ gs.countP (fun g => refsWire g a) :=
    countP_eraseIdx_succ_le _ gs p hp href
  have h3 : (gs.eraseIdx p).countP (fun g => refsWire g (n + p)) ≤ fanOut n gs p :=
    (List.eraseIdx_sublist gs p).countP_le
  have h4 : gs.countP (fun g => refsWire g a) = fanOut n gs q := by
    simp only [fanOut, hqa]
  omega

theorem numReconv_contract_le (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hp : p < gs.length)
    (href : refsWire (gs.get ⟨p, hp⟩) a = true) :
    numReconv n (contract n p a inv gs) ≤ numReconv n gs := by
  have hlt : a < n + p := by
    have h := hwf ⟨p, hp⟩
    have hr := href
    simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with h' | h'
    · rw [← h']; exact h.1
    · rw [← h']; exact h.2
  obtain ⟨m, hm'⟩ : ∃ m, gs.length = p + (1 + m) := ⟨gs.length - p - 1, by omega⟩
  have hlen : (contract n p a inv gs).length = p + m := by
    rw [length_contract n p a inv gs hp]; omega
  have Enew : numReconv n (contract n p a inv gs)
      = (List.range p).countP (fun q => decide (2 ≤ fanOut n (contract n p a inv gs) q))
        + (List.range m).countP
            (fun j => decide (2 ≤ fanOut n (contract n p a inv gs) (p + j))) := by
    rw [numReconv, hlen, countP_range_split]
  have key2 : (List.range m).countP
        (fun j => decide (2 ≤ fanOut n (contract n p a inv gs) (p + j)))
      ≤ (List.range m).countP (fun j => decide (2 ≤ fanOut n gs (p + (1 + j)))) := by
    refine List.countP_mono_left (fun j _ h => ?_)
    simp only [decide_eq_true_eq] at h ⊢
    have hqa : n + (p + j) ≠ a := by omega
    have hb := fanOut_contract_le n gs p a (p + j) inv hqa
    have ho : oldIdx p (p + j) = p + (1 + j) := by unfold oldIdx; split <;> omega
    rw [ho] at hb
    omega
  by_cases hfp : 2 ≤ fanOut n gs p
  · have Eold : numReconv n gs
        = (List.range p).countP (fun q => decide (2 ≤ fanOut n gs q))
          + (1 + (List.range m).countP
              (fun j => decide (2 ≤ fanOut n gs (p + (1 + j))))) := by
      rw [numReconv, hm', countP_range_split, countP_range_split]
      simp [hfp]
    have key1 : (List.range p).countP
          (fun q => decide (2 ≤ fanOut n (contract n p a inv gs) q))
        ≤ (List.range p).countP (fun q => decide (2 ≤ fanOut n gs q)) + 1 := by
      have hme := countP_mono_except
        (fun q => decide (2 ≤ fanOut n (contract n p a inv gs) q))
        (fun q => decide (2 ≤ fanOut n gs q)) (a - n) (List.range p)
        (by
          intro q hq hqc h
          have hqp : q < p := List.mem_range.mp hq
          have hqa : n + q ≠ a := by omega
          simp only [decide_eq_true_eq] at h ⊢
          have hb := fanOut_contract_le n gs p a q inv hqa
          have ho : oldIdx p q = q := by unfold oldIdx; split <;> omega
          rw [ho] at hb
          omega)
      have hone : (List.range p).countP (fun x => decide (x = a - n)) ≤ 1 := by
        rw [countP_eq_range]; split <;> omega
      omega
    omega
  · have Eold : numReconv n gs
        = (List.range p).countP (fun q => decide (2 ≤ fanOut n gs q))
          + (0 + (List.range m).countP
              (fun j => decide (2 ≤ fanOut n gs (p + (1 + j))))) := by
      rw [numReconv, hm', countP_range_split, countP_range_split]
      simp [hfp]
    have key1 : (List.range p).countP
          (fun q => decide (2 ≤ fanOut n (contract n p a inv gs) q))
        ≤ (List.range p).countP (fun q => decide (2 ≤ fanOut n gs q)) := by
      refine List.countP_mono_left (fun q hq h => ?_)
      have hqp : q < p := List.mem_range.mp hq
      simp only [decide_eq_true_eq] at h ⊢
      by_cases hqa : n + q = a
      · have hb := fanOut_contract_a_le n gs p a q inv hlt hqa hp href
        omega
      · have hb := fanOut_contract_le n gs p a q inv hqa
        have ho : oldIdx p q = q := by unfold oldIdx; split <;> omega
        rw [ho] at hb
        omega
    omega

private def ctrGs : List Gate :=
  [⟨false, 0, false, 1⟩, ⟨false, 2, false, 2⟩, ⟨false, 3, false, 0⟩, ⟨false, 3, false, 1⟩]

theorem ctr_contract_eq :
    contract 2 1 2 false ctrGs
      = [⟨false, 0, false, 1⟩, ⟨false, 2, false, 0⟩, ⟨false, 2, false, 1⟩] := by
  rfl

theorem ctr_counts :
    numReconv 2 ctrGs = 1 ∧ numReconv 2 (contract 2 1 2 false ctrGs) = 1 ∧
    fanOut 2 ctrGs 1 = 2 ∧ fanOut 2 (contract 2 1 2 false ctrGs) 0 = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem ctr_wf_after : wfC 2 (contract 2 1 2 false ctrGs) := by
  rw [ctr_contract_eq]
  intro q
  obtain ⟨i, hi⟩ := q
  simp only [List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by simp, by simp⟩
  | 1, _ => exact ⟨by simp, by simp⟩
  | 2, _ => exact ⟨by simp, by simp⟩
  | (k + 3), h => exact absurd h (by omega)

private def badGs : List Gate :=
  [⟨false, 0, false, 0⟩, ⟨false, 0, false, 0⟩, ⟨false, 1, false, 0⟩, ⟨false, 2, false, 0⟩]

theorem contract_needs_refs :
    wfC 1 badGs ∧ (1 : Nat) < badGs.length
      ∧ refsWire (badGs.get ⟨1, by decide⟩) 1 = false
      ∧ numReconv 1 badGs = 0
      ∧ numReconv 1 (contract 1 1 1 false badGs) = 1 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro q
  obtain ⟨i, hi⟩ := q
  simp only [badGs, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by show (0:Nat) < 1; decide, by show (0:Nat) < 1; decide⟩
  | 1, _ => exact ⟨by show (0:Nat) < 2; decide, by show (0:Nat) < 2; decide⟩
  | 2, _ => exact ⟨by show (1:Nat) < 3; decide, by show (0:Nat) < 3; decide⟩
  | 3, _ => exact ⟨by show (2:Nat) < 4; decide, by show (0:Nat) < 4; decide⟩
  | (k + 4), h => exact absurd h (by omega)

private def polGs : List Gate := [⟨false, 0, false, 0⟩, ⟨true, 2, true, 2⟩, ⟨false, 3, false, 1⟩]
private def polF : Func 2 := fun x => (!x 0) && x 1
private def polX_FT : Assign 2 := fun j => if j.val = 0 then false else true
private def polX_FF : Assign 2 := fun _ => false

theorem contract_needs_polarity :
    IsPassThroughAt 2 polGs 1 2 true
      ∧ CircuitComputes (contract 2 1 2 true polGs) polF
      ∧ ¬ CircuitComputes (contract 2 1 2 false polGs) polF := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [polGs, evalGates, wireVal]
  · refine Or.inl ?_
    intro x
    simp [polGs, polF, contract, contractGate, contractWire, circuitOut, evalGates, wireVal]
  · rintro (h | h)
    · have hx := h polX_FT
      simp [polGs, polF, polX_FT, contract, contractGate, contractWire, circuitOut, evalGates,
        wireVal] at hx
    · have hx := h polX_FF
      simp [polGs, polF, polX_FF, contract, contractGate, contractWire, circuitOut, evalGates,
        wireVal] at hx

#print axioms length_contract
#print axioms contract_needs_polarity
#print axioms ctr_contract_eq
#print axioms ctr_counts
#print axioms ctr_wf_after
#print axioms contract_needs_refs
#print axioms numReconv_contract_le

private theorem getD_push_self' (v : Array Bool) (b : Bool) (j : Nat) (h : j = v.size) :
    (v.push b).getD j false = b := by subst h; exact getD_push_self v b

private theorem contractWire_lt (n p a w j : Nat) (ha : a < n + p) (hpj : p ≤ j)
    (hw : w < n + j + 1) : contractWire n p a w < n + j := by
  unfold contractWire
  split
  · omega
  · split <;> omega

theorem wfC_contract (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC n gs) (hp : p < gs.length) (ha : a < n + p) :
    wfC n (contract n p a inv gs) := by
  intro q
  obtain ⟨j, hj⟩ := q
  simp only [List.get_eq_getElem]
  have hlm : (contract n p a inv gs).length = (gs.eraseIdx p).length := by
    simp only [contract, List.length_map]
  have hje : j < (gs.eraseIdx p).length := by rw [← hlm]; exact hj
  have hel : (gs.eraseIdx p).length = gs.length - 1 := by
    rw [List.length_eraseIdx, if_pos hp]
  have hget : (contract n p a inv gs)[j] = contractGate n p a inv ((gs.eraseIdx p)[j]) := by
    simp only [contract]; exact List.getElem_map _
  rw [hget]
  by_cases hjp : j < p
  · have h1 : (gs.eraseIdx p)[j] = gs[j] := List.getElem_eraseIdx_of_lt hje hjp
    have hjg : j < gs.length := by omega
    have hw := hwf ⟨j, hjg⟩
    simp only [List.get_eq_getElem] at hw
    rw [h1, contractGate_id n p a inv gs[j] (by omega) (by omega)]
    exact hw
  · have h1 : (gs.eraseIdx p)[j] = gs[j + 1] := List.getElem_eraseIdx_of_ge hje (by omega)
    have hjg : j + 1 < gs.length := by omega
    have hw := hwf ⟨j + 1, hjg⟩
    simp only [List.get_eq_getElem] at hw
    rw [h1]
    exact ⟨contractWire_lt n p a _ j ha (by omega) (by omega),
           contractWire_lt n p a _ j ha (by omega) (by omega)⟩

theorem wfC_take (n : Nat) (gs : List Gate) (k : Nat) (hwf : wfC n gs) : wfC n (gs.take k) := by
  intro q
  obtain ⟨j, hj⟩ := q
  simp only [List.get_eq_getElem]
  have hlen : (gs.take k).length = min k gs.length := List.length_take
  have hjg : j < gs.length := by omega
  have hw := hwf ⟨j, hjg⟩
  simp only [List.get_eq_getElem] at hw
  rw [List.getElem_take]
  exact hw

theorem getD_evalGates_take (n : Nat) (x : Assign n) (gs : List Gate) (j : Nat)
    (hj : j < gs.length) :
    (evalGates x gs).getD j false = (evalGates x (gs.take (j + 1))).getD j false := by
  have key : ∀ l : List Gate, l = gs.take (j + 1) ++ gs.drop (j + 1) →
      evalGates x l = (gs.drop (j + 1)).foldl (gstep x) (evalGates x (gs.take (j + 1))) := by
    intro l hl
    rw [hl, evalGates_foldl, List.foldl_append, evalGates_foldl]
  rw [key gs (List.take_append_drop _ _).symm]
  refine getD_foldl_lt x _ _ j ?_
  rw [size_evalGates, List.length_take]
  omega

theorem getD_evalGates_eq (n : Nat) (x : Assign n) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC n gs) :
    (evalGates x gs).getD p false
      = ((xor (gs[p]).na (wireVal x (evalGates x gs) (gs[p]).ia))
        && (xor (gs[p]).nb (wireVal x (evalGates x gs) (gs[p]).ib))) := by
  have hdec : gs.take p ++ gs[p] :: gs.drop (p + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have key : ∀ l : List Gate, l = gs.take p ++ gs[p] :: gs.drop (p + 1) →
      evalGates x l = (gs.drop (p + 1)).foldl (gstep x)
        (gstep x (evalGates x (gs.take p)) gs[p]) := by
    intro l hl
    rw [hl, evalGates_foldl, List.foldl_append, List.foldl_cons, evalGates_foldl]
  have hE := key gs hdec.symm
  have hPs : (evalGates x (gs.take p)).size = p := by
    rw [size_evalGates, List.length_take]; omega
  have hWs : (gstep x (evalGates x (gs.take p)) gs[p]).size = p + 1 := by
    unfold gstep; simp [hPs]
  have hw := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hw
  have hWV : ∀ w, w < n + p →
      wireVal x (evalGates x gs) w = wireVal x (evalGates x (gs.take p)) w := by
    intro w hwlt
    rw [hE, wireVal_foldl x _ _ w (by omega)]
    by_cases hn : w < n
    · rw [wireVal_lt x _ w hn, wireVal_lt x _ w hn]
    · rw [wireVal_ge x _ w hn, wireVal_ge x _ w hn]
      unfold gstep
      exact getD_push_ne _ _ (w - n) (by omega)
  have hL : (evalGates x gs).getD p false
      = (gstep x (evalGates x (gs.take p)) gs[p]).getD p false := by
    rw [hE]; exact getD_foldl_lt x _ _ p (by omega)
  have hL2 : (gstep x (evalGates x (gs.take p)) gs[p]).getD p false
      = ((xor (gs[p]).na (wireVal x (evalGates x (gs.take p)) (gs[p]).ia))
        && (xor (gs[p]).nb (wireVal x (evalGates x (gs.take p)) (gs[p]).ib))) := by
    unfold gstep
    exact getD_push_self' _ _ p hPs.symm
  rw [hL, hL2, hWV _ hw.1, hWV _ hw.2]

theorem dup_wire_passthrough (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC n gs) (hia : (gs[p]).ia = (gs[p]).ib) (hna : (gs[p]).na = (gs[p]).nb) :
    IsPassThroughAt n gs p (gs[p]).ia (gs[p]).na := by
  intro x
  rw [getD_evalGates_eq n x gs p hp hwf, ← hia, ← hna]
  simp

theorem dup_wire_const (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC n gs) (hia : (gs[p]).ia = (gs[p]).ib) (hna : (gs[p]).na ≠ (gs[p]).nb)
    (x : Assign n) : (evalGates x gs).getD p false = false := by
  rw [getD_evalGates_eq n x gs p hp hwf, ← hia]
  revert hna
  cases (gs[p]).na <;> cases (gs[p]).nb <;>
    cases (wireVal x (evalGates x gs) (gs[p]).ia) <;> simp

theorem opt_no_passthrough (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p a : Nat) (inv : Bool) (hp : p < gs.length) (ha : a < n + p)
    (hcase : n ≤ a ∨ p + 1 < gs.length)
    (hpt : IsPassThroughAt n gs p a inv) : False := by
  by_cases hout : p + 1 < gs.length
  · have hcc := circuitOut_contract n gs p a inv hwf hout ha hpt f hc
    have hw' := wfC_contract n gs p a inv hwf hp ha
    have hlc := length_contract n p a inv gs hp
    have hhc : HasCircuit f (m - 1) := ⟨contract n p a inv gs, hw', by omega, hcc⟩
    have := hopt.2 (m - 1) hhc
    omega
  · have hpe : p + 1 = gs.length := by omega
    have han : n ≤ a := by
      rcases hcase with h | h
      · exact h
      · omega
    have hjg : a - n < gs.length := by omega
    have hstep : ∀ x : Assign n,
        circuitOut x (gs.take (a - n + 1)) = xor inv (circuitOut x gs) := by
      intro x
      unfold circuitOut
      rw [show (gs.take (a - n + 1)).length = a - n + 1 from by rw [List.length_take]; omega,
          show a - n + 1 - 1 = a - n from by omega,
          ← getD_evalGates_take n x gs (a - n) hjg,
          show gs.length - 1 = p from by omega, hpt x,
          wireVal_ge x (evalGates x gs) a (by omega)]
      cases inv <;> simp
    have hcomp : CircuitComputes (gs.take (a - n + 1)) f := by
      rcases hc with h | h
      · cases inv with
        | false => exact Or.inl (fun x => by rw [hstep x, h x]; simp)
        | true => exact Or.inr (fun x => by rw [hstep x, h x]; simp)
      · cases inv with
        | false => exact Or.inr (fun x => by rw [hstep x, h x]; simp)
        | true => exact Or.inl (fun x => by rw [hstep x, h x]; simp)
    have hhc : HasCircuit f (a - n + 1) :=
      ⟨gs.take (a - n + 1), wfC_take n gs _ hwf, by rw [List.length_take]; omega, hcomp⟩
    have := hopt.2 _ hhc
    omega

theorem opt_no_dup_gate_wire (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p < gs.length) (hn : n ≤ (gs[p]).ia)
    (hia : (gs[p]).ia = (gs[p]).ib) (hna : (gs[p]).na = (gs[p]).nb) : False := by
  have hw := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hw
  exact opt_no_passthrough n f gs m hwf hopt hlen hc p (gs[p]).ia (gs[p]).na hp hw.1
    (Or.inl hn) (dup_wire_passthrough n gs p hp hwf hia hna)

theorem opt_no_dup_gate_wire_output (n : Nat) (f : Func n) (gs : List Gate)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC n gs) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p < gs.length) (hlast : p + 1 = gs.length)
    (hia : (gs[p]).ia = (gs[p]).ib) (hna : (gs[p]).na ≠ (gs[p]).nb) : False := by
  have hconst : ∀ x : Assign n, circuitOut x gs = false := by
    intro x
    unfold circuitOut
    rw [show gs.length - 1 = p from by omega]
    exact dup_wire_const n gs p hp hwf hia hna x
  rcases hc with h | h
  · refine h0 (funext fun x => ?_)
    rw [← h x]; exact hconst x
  · refine h1 (funext fun x => ?_)
    have hx := h x
    rw [hconst x] at hx
    cases hfx : f x
    · rw [hfx] at hx; simp at hx
    · rfl

#print axioms wfC_contract
#print axioms wfC_take
#print axioms getD_evalGates_eq
#print axioms dup_wire_passthrough
#print axioms dup_wire_const
#print axioms opt_no_passthrough
#print axioms opt_no_dup_gate_wire
#print axioms opt_no_dup_gate_wire_output

def NoConsumer (n : Nat) (gs : List Gate) (p : Nat) : Prop := fanOut n gs p = 0

theorem noRefs_of_noConsumer (n : Nat) (gs : List Gate) (p : Nat) (hnc : NoConsumer n gs p) :
    ∀ g ∈ gs, refsWire g (n + p) = false := by
  intro g hg
  have h := (List.countP_eq_zero).mp hnc g hg
  simpa using h

theorem contract_eq_of_noConsumer (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hnc : NoConsumer n gs p) : contract n p a inv gs = contract n p 0 false gs := by
  have hsub : gs.eraseIdx p ⊆ gs := (List.eraseIdx_sublist gs p).subset
  simp only [contract]
  refine List.map_congr_left ?_
  intro g hg
  have hr := noRefs_of_noConsumer n gs p hnc g (hsub hg)
  simp only [refsWire, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
  unfold contractGate contractWire
  simp [hr.1, hr.2]

def dropDead (n : Nat) (gs : List Gate) (p : Nat) : List Gate := contract n p 0 false gs

theorem length_dropDead (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length) :
    (dropDead n gs p).length = gs.length - 1 := length_contract n p 0 false gs hp

theorem wfC_dropDead (n : Nat) (gs : List Gate) (p : Nat) (hwf : wfC n gs) (hp : p < gs.length) :
    wfC n (dropDead n gs p) := by
  have hw := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hw
  exact wfC_contract n gs p 0 false hwf hp (by omega)

theorem evalGates_dropDead (n : Nat) (gs : List Gate) (p : Nat)
    (hwf : wfC n gs) (hp : p < gs.length) (hnc : NoConsumer n gs p) (x : Assign n) :
    ∀ q, q < gs.length - 1 →
      (evalGates x (dropDead n gs p)).getD q false
        = (evalGates x gs).getD (oldIdx p q) false := by
  intro q hq
  have hw := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hw
  have heq : (evalGates x gs).getD p false
      = xor (xor ((evalGates x gs).getD p false)
              (wireVal x (evalGates x gs) (gs[p]).ia))
            (wireVal x (evalGates x gs) (gs[p]).ia) := by
    cases (evalGates x gs).getD p false <;>
      cases wireVal x (evalGates x gs) (gs[p]).ia <;> simp
  have hce := contract_eq_of_noConsumer n gs p (gs[p]).ia
      (xor ((evalGates x gs).getD p false) (wireVal x (evalGates x gs) (gs[p]).ia)) hnc
  rw [dropDead, ← hce]
  exact evalGates_contract n gs p _ _ hwf hp hw.1 x heq q hq

theorem circuitOut_dropDead (n : Nat) (gs : List Gate) (p : Nat)
    (hwf : wfC n gs) (hp : p + 1 < gs.length) (hnc : NoConsumer n gs p) (x : Assign n) :
    circuitOut x (dropDead n gs p) = circuitOut x gs := by
  unfold circuitOut
  rw [length_dropDead n gs p (by omega),
      evalGates_dropDead n gs p hwf (by omega) hnc x _ (by omega)]
  have ho : oldIdx p (gs.length - 1 - 1) = gs.length - 1 := by
    unfold oldIdx
    rw [if_neg (show ¬ (gs.length - 1 - 1 < p) from by omega)]
    omega
  rw [ho]

theorem circuitComputes_dropDead (n : Nat) (gs : List Gate) (p : Nat) (f : Func n)
    (hwf : wfC n gs) (hp : p + 1 < gs.length) (hnc : NoConsumer n gs p)
    (hc : CircuitComputes gs f) : CircuitComputes (dropDead n gs p) f := by
  rcases hc with h | h
  · exact Or.inl (fun x => by rw [circuitOut_dropDead n gs p hwf hp hnc x]; exact h x)
  · exact Or.inr (fun x => by rw [circuitOut_dropDead n gs p hwf hp hnc x]; exact h x)

theorem opt_no_dead_gate (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p + 1 < gs.length) (hnc : NoConsumer n gs p) : False := by
  have hhc : HasCircuit f (m - 1) :=
    ⟨dropDead n gs p, wfC_dropDead n gs p hwf (by omega),
     by rw [length_dropDead n gs p (by omega)]; omega,
     circuitComputes_dropDead n gs p f hwf hp hnc hc⟩
  have := hopt.2 _ hhc
  omega

private def ddGs : List Gate :=
  [⟨false, 0, false, 1⟩, ⟨false, 0, false, 0⟩, ⟨false, 2, false, 1⟩]

theorem dd_control :
    NoConsumer 2 ddGs 1
      ∧ dropDead 2 ddGs 1 = [⟨false, 0, false, 1⟩, ⟨false, 2, false, 1⟩]
      ∧ contract 2 1 7 true ddGs = dropDead 2 ddGs 1
      ∧ (dropDead 2 ddGs 1).length + 1 = ddGs.length := by
  refine ⟨by unfold NoConsumer; decide, by rfl, by rfl, by rfl⟩

theorem dd_computes :
    ∀ x : Assign 2, circuitOut x (dropDead 2 ddGs 1) = circuitOut x ddGs := by
  intro x
  simp [ddGs, dropDead, contract, contractGate, contractWire, circuitOut, evalGates, wireVal]

#print axioms contract_eq_of_noConsumer
#print axioms evalGates_dropDead
#print axioms circuitOut_dropDead
#print axioms opt_no_dead_gate
#print axioms dd_control
#print axioms dd_computes

def IsConstGate (n : Nat) (gs : List Gate) (p : Nat) (c : Bool) : Prop :=
  ∀ x : Assign n, (evalGates x gs).getD p false = c

theorem const_consumer (n : Nat) (gs : List Gate) (p r : Nat) (c : Bool)
    (hwf : wfC n gs) (hr : r < gs.length) (hcst : IsConstGate n gs p c)
    (hrefs : refsWire gs[r] (n + p) = true) :
    IsConstGate n gs r false ∨
      (∃ (a : Nat) (inv : Bool), a < n + r ∧ IsPassThroughAt n gs r a inv) := by
  have hw := hwf ⟨r, hr⟩
  simp only [List.get_eq_getElem] at hw
  have hval : ∀ x : Assign n, (evalGates x gs).getD r false
      = ((xor (gs[r]).na (wireVal x (evalGates x gs) (gs[r]).ia))
        && (xor (gs[r]).nb (wireVal x (evalGates x gs) (gs[r]).ib))) :=
    fun x => getD_evalGates_eq n x gs r hr hwf
  have hcp : ∀ x : Assign n, wireVal x (evalGates x gs) (n + p) = c := by
    intro x
    rw [wireVal_ge x (evalGates x gs) (n + p) (by omega)]
    have he : n + p - n = p := by omega
    rw [he]
    exact hcst x
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hrefs
  rcases hrefs with hia | hib
  · by_cases hz : xor (gs[r]).na c = false
    · refine Or.inl (fun x => ?_)
      rw [hval x, hia, hcp x, hz]
      simp
    · refine Or.inr ⟨(gs[r]).ib, (gs[r]).nb, hw.2, fun x => ?_⟩
      rw [hval x, hia, hcp x]
      have hz' : xor (gs[r]).na c = true := by
        cases h : xor (gs[r]).na c
        · exact absurd h hz
        · rfl
      rw [hz']
      simp
  · by_cases hz : xor (gs[r]).nb c = false
    · refine Or.inl (fun x => ?_)
      rw [hval x, hib, hcp x, hz]
      simp
    · refine Or.inr ⟨(gs[r]).ia, (gs[r]).na, hw.1, fun x => ?_⟩
      rw [hval x, hib, hcp x]
      have hz' : xor (gs[r]).nb c = true := by
        cases h : xor (gs[r]).nb c
        · exact absurd h hz
        · rfl
      rw [hz']
      simp

theorem opt_no_output_input_passthrough (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (r a : Nat) (inv : Bool) (hrout : r + 1 = gs.length) (h2 : 2 ≤ gs.length) (han : a < n)
    (hpt : IsPassThroughAt n gs r a inv) : False := by
  have hout : ∀ x : Assign n, circuitOut x gs = xor inv (x ⟨a, han⟩) := by
    intro x
    unfold circuitOut
    rw [show gs.length - 1 = r from by omega, hpt x, wireVal_lt x (evalGates x gs) a han]
  have hg1wf : wfC n [(⟨false, a, false, a⟩ : Gate)] := by
    intro qq
    obtain ⟨j, hj⟩ := qq
    simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact ⟨by simpa using han, by simpa using han⟩
    | (t + 1), hh => exact absurd hh (by omega)
  have hg1out : ∀ x : Assign n, circuitOut x [(⟨false, a, false, a⟩ : Gate)] = x ⟨a, han⟩ := by
    intro x
    simp [circuitOut, evalGates, wireVal, han]
  have hfe : ∃ e : Bool, ∀ x : Assign n, f x = xor e (x ⟨a, han⟩) := by
    rcases hc with h | h
    · exact ⟨inv, fun x => by rw [← h x, hout x]⟩
    · refine ⟨!inv, fun x => ?_⟩
      have e1 := h x
      rw [hout x] at e1
      cases inv <;> cases hxa : x ⟨a, han⟩ <;> simp_all
  obtain ⟨e, he⟩ := hfe
  have hcomp : CircuitComputes [(⟨false, a, false, a⟩ : Gate)] f := by
    cases e with
    | false => exact Or.inl (fun x => by rw [hg1out x, he x]; simp)
    | true => exact Or.inr (fun x => by rw [hg1out x, he x]; simp)
  have hhc : HasCircuit f 1 := ⟨[(⟨false, a, false, a⟩ : Gate)], hg1wf, by simp, hcomp⟩
  have := hopt.2 1 hhc
  omega

private theorem no_const_aux (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f) :
    ∀ (k p : Nat) (c : Bool), gs.length - p ≤ k → p < gs.length → IsConstGate n gs p c → False
  | 0, p, _, hk, hp, _ => by omega
  | (k + 1), p, c, hk, hp, hcst => by
      by_cases hout : p + 1 = gs.length
      · have hconst : ∀ x : Assign n, circuitOut x gs = c := by
          intro x
          unfold circuitOut
          rw [show gs.length - 1 = p from by omega]
          exact hcst x
        rcases hc with h | h
        · cases c with
          | false => exact h0 (funext fun x => by rw [← h x]; exact hconst x)
          | true => exact h1 (funext fun x => by rw [← h x]; exact hconst x)
        · cases c with
          | false =>
            refine h1 (funext fun x => ?_)
            have hx := h x
            rw [hconst x] at hx
            cases hfx : f x
            · rw [hfx] at hx; simp at hx
            · rfl
          | true =>
            refine h0 (funext fun x => ?_)
            have hx := h x
            rw [hconst x] at hx
            cases hfx : f x
            · rfl
            · rw [hfx] at hx; simp at hx
      · have hplt : p + 1 < gs.length := by omega
        by_cases hdead : fanOut n gs p = 0
        · exact opt_no_dead_gate n f gs m hwf hopt hlen hc p hplt hdead
        · have hex : ∃ (r : Nat) (hr : r < gs.length), refsWire gs[r] (n + p) = true := by
            refine Classical.byContradiction (fun hcon => ?_)
            apply hdead
            unfold fanOut
            rw [List.countP_eq_zero]
            intro g hg
            rw [List.mem_iff_getElem] at hg
            obtain ⟨j, hj, rfl⟩ := hg
            intro habs
            exact hcon ⟨j, hj, habs⟩
          obtain ⟨r, hr, hrefs⟩ := hex
          have hwr := hwf ⟨r, hr⟩
          simp only [List.get_eq_getElem] at hwr
          have hpr : p < r := by
            simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hrefs
            rcases hrefs with hh | hh <;> omega
          rcases const_consumer n gs p r c hwf hr hcst hrefs with hcr | ⟨a, inv, haw, hpt⟩
          · exact no_const_aux n f gs m h0 h1 hwf hopt hlen hc k r false (by omega) hr hcr
          · by_cases hrout : r + 1 < gs.length
            · exact opt_no_passthrough n f gs m hwf hopt hlen hc r a inv hr haw
                (Or.inr hrout) hpt
            · by_cases han : n ≤ a
              · exact opt_no_passthrough n f gs m hwf hopt hlen hc r a inv hr haw
                  (Or.inl han) hpt
              · exact opt_no_output_input_passthrough n f gs m hwf hopt hlen hc r a inv
                  (by omega) (by omega) (by omega) hpt

theorem opt_no_const_gate (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p < gs.length) (c : Bool) (hcst : IsConstGate n gs p c) : False :=
  no_const_aux n f gs m h0 h1 hwf hopt hlen hc (gs.length) p c (by omega) hp hcst

#print axioms const_consumer
#print axioms opt_no_output_input_passthrough
#print axioms opt_no_const_gate

theorem opt_no_dup_gate_wire_full (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p < gs.length) (hn : n ≤ (gs[p]).ia)
    (hia : (gs[p]).ia = (gs[p]).ib) : False := by
  by_cases hna : (gs[p]).na = (gs[p]).nb
  · exact opt_no_dup_gate_wire n f gs m hwf hopt hlen hc p hp hn hia hna
  · exact opt_no_const_gate n f gs m h0 h1 hwf hopt hlen hc p hp false
      (fun x => dup_wire_const n gs p hp hwf hia hna x)

private theorem sum_map_ite_eq_countP {α : Type} (f : α → Bool) :
    ∀ l : List α, (l.map (fun g => if f g then 1 else 0)).sum = l.countP f
  | [] => rfl
  | g :: t => by
      simp only [List.map_cons, List.sum_cons, List.countP_cons, sum_map_ite_eq_countP f t]
      by_cases h : f g = true <;> simp [h] <;> omega

theorem fanOut_eq_fanOutEdges_of_opt (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (q : Nat) : fanOut n gs q = fanOutEdges n gs q := by
  have hpt : ∀ g ∈ gs, edgesTo g (n + q) = if refsWire g (n + q) then 1 else 0 := by
    intro g hg
    rw [List.mem_iff_getElem] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    have hne : ¬ ((gs[j]).ia = (gs[j]).ib ∧ (gs[j]).ia = n + q) := by
      intro hboth
      exact opt_no_dup_gate_wire_full n f gs m h0 h1 hwf hopt hlen hc j hj
        (by omega) hboth.1
    unfold edgesTo refsWire
    by_cases hA : (gs[j]).ia = n + q
    · by_cases hB : (gs[j]).ib = n + q
      · exact absurd ⟨by omega, hA⟩ hne
      · simp [hA, hB]
    · by_cases hB : (gs[j]).ib = n + q
      · simp [hA, hB]
      · simp [hA, hB]
  unfold fanOut fanOutEdges
  rw [List.map_congr_left hpt, sum_map_ite_eq_countP]

#print axioms opt_no_dup_gate_wire_full
#print axioms fanOut_eq_fanOutEdges_of_opt

def snocT {n : Nat} (x : Assign n) (b : Bool) : Assign (n + 1) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else b

theorem dropLast_snocT {n : Nat} (x : Assign n) (b : Bool) : dropLast (snocT x b) = x := by
  funext i
  obtain ⟨j, hj⟩ := i
  simp [dropLast, snocT, Fin.castSucc, Fin.castAdd, Fin.castLE, hj]

theorem snocT_last {n : Nat} (x : Assign n) (b : Bool) : snocT x b (Fin.last n) = b := by
  simp [snocT, Fin.last]

def dropWire (n w : Nat) : Nat := if w < n then w else w - 1

def dropGate (n : Nat) (g : Gate) : Gate :=
  ⟨g.na, dropWire n g.ia, g.nb, dropWire n g.ib⟩

def dropVar (n : Nat) (gs : List Gate) : List Gate := gs.map (dropGate n)

def NoRefVar (n : Nat) (gs : List Gate) : Prop := ∀ g ∈ gs, g.ia ≠ n ∧ g.ib ≠ n

theorem length_dropVar (n : Nat) (gs : List Gate) : (dropVar n gs).length = gs.length := by
  simp [dropVar]

theorem wireVal_drop {n : Nat} (x : Assign n) (b : Bool) (vals : Array Bool) (w : Nat)
    (hw : w ≠ n) : wireVal (snocT x b) vals w = wireVal x vals (dropWire n w) := by
  by_cases hlt : w < n
  · have hd : dropWire n w = w := by unfold dropWire; simp [hlt]
    rw [hd, wireVal_lt (snocT x b) vals w (by omega), wireVal_lt x vals w hlt]
    simp [snocT, hlt]
  · have hd : dropWire n w = w - 1 := by unfold dropWire; simp [hlt]
    rw [hd, wireVal_ge (snocT x b) vals w (by omega), wireVal_ge x vals (w - 1) (by omega)]
    congr 1
    omega

theorem foldl_drop {n : Nat} (x : Assign n) (b : Bool) :
    ∀ (gs : List Gate), NoRefVar n gs → ∀ acc : Array Bool,
      (gs.map (dropGate n)).foldl (gstep x) acc = gs.foldl (gstep (snocT x b)) acc
  | [], _, _ => rfl
  | g :: t, hno, acc => by
      have hg := hno g (by simp)
      simp only [List.map_cons, List.foldl_cons]
      have hstep : gstep x acc (dropGate n g) = gstep (snocT x b) acc g := by
        simp [gstep, dropGate, wireVal_drop x b acc g.ia hg.1, wireVal_drop x b acc g.ib hg.2]
      rw [hstep, foldl_drop x b t (fun y hy => hno y (by simp [hy])) _]

theorem evalGates_dropVar {n : Nat} (x : Assign n) (b : Bool) (gs : List Gate)
    (hno : NoRefVar n gs) : evalGates x (dropVar n gs) = evalGates (snocT x b) gs := by
  rw [evalGates_foldl, evalGates_foldl, dropVar, foldl_drop x b gs hno]

theorem circuitOut_dropVar {n : Nat} (x : Assign n) (b : Bool) (gs : List Gate)
    (hno : NoRefVar n gs) : circuitOut x (dropVar n gs) = circuitOut (snocT x b) gs := by
  unfold circuitOut
  rw [length_dropVar, evalGates_dropVar x b gs hno]

theorem wfC_dropVar (n : Nat) (gs : List Gate) (hwf : wfC (n + 1) gs) (hno : NoRefVar n gs) :
    wfC n (dropVar n gs) := by
  intro q
  obtain ⟨j, hj⟩ := q
  simp only [List.get_eq_getElem]
  have hlm : (dropVar n gs).length = gs.length := length_dropVar n gs
  have hjg : j < gs.length := by omega
  have hw := hwf ⟨j, hjg⟩
  simp only [List.get_eq_getElem] at hw
  have hno' := hno gs[j] (List.getElem_mem hjg)
  have hget : (dropVar n gs)[j] = dropGate n gs[j] := by
    simp only [dropVar]; exact List.getElem_map _
  rw [hget]
  refine ⟨?_, ?_⟩
  · unfold dropGate dropWire; simp only []; split <;> omega
  · unfold dropGate dropWire; simp only []; split <;> omega

private theorem contractWire_ne (n p a w : Nat) (hane : a ≠ n) (hw : w ≠ n) :
    contractWire (n + 1) p a w ≠ n := by
  unfold contractWire
  split
  · exact hane
  · split <;> omega

theorem passthrough_of_soleReader (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC (n + 1) gs) (hp : p < gs.length) (hgate : gs[p] = ⟨inv, a, false, n⟩)
    (x : Assign n) :
    (evalGates (snocT x true) gs).getD p false
      = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a) := by
  rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hgate]
  have hn : wireVal (snocT x true) (evalGates (snocT x true) gs) n = true := by
    rw [wireVal_lt (snocT x true) _ n (by omega)]
    simp [snocT]
  simp [hn]

theorem noRefVar_contract (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hp : p < gs.length) (hane : a ≠ n)
    (huniq : ∀ (q : Nat) (hq : q < gs.length), q ≠ p → gs[q].ia ≠ n ∧ gs[q].ib ≠ n) :
    NoRefVar n (contract (n + 1) p a inv gs) := by
  intro g hg
  rw [contract, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  rw [List.mem_iff_getElem] at hg0
  obtain ⟨j, hj, rfl⟩ := hg0
  have hel : (gs.eraseIdx p).length = gs.length - 1 := by
    rw [List.length_eraseIdx, if_pos hp]
  have hw : (gs.eraseIdx p)[j].ia ≠ n ∧ (gs.eraseIdx p)[j].ib ≠ n := by
    by_cases hjp : j < p
    · rw [List.getElem_eraseIdx_of_lt hj hjp]
      exact huniq j (by omega) (by omega)
    · rw [List.getElem_eraseIdx_of_ge hj (by omega)]
      exact huniq (j + 1) (by omega) (by omega)
  exact ⟨contractWire_ne n p a _ hane hw.1, contractWire_ne n p a _ hane hw.2⟩

def restrictTrue (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool) : List Gate :=
  dropVar n (contract (n + 1) p a inv gs)

theorem length_restrictTrue (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hp : p < gs.length) : (restrictTrue n gs p a inv).length = gs.length - 1 := by
  rw [restrictTrue, length_dropVar, length_contract (n + 1) p a inv gs hp]

theorem wfC_restrictTrue (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC (n + 1) gs) (hp : p < gs.length) (ha : a < (n + 1) + p) (hane : a ≠ n)
    (huniq : ∀ (q : Nat) (hq : q < gs.length), q ≠ p → gs[q].ia ≠ n ∧ gs[q].ib ≠ n) :
    wfC n (restrictTrue n gs p a inv) :=
  wfC_dropVar n _ (wfC_contract (n + 1) gs p a inv hwf hp ha)
    (noRefVar_contract n gs p a inv hp hane huniq)

theorem circuitOut_restrictTrue (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hwf : wfC (n + 1) gs) (hp : p < gs.length) (hgate : gs[p] = ⟨inv, a, false, n⟩)
    (hane : a ≠ n)
    (huniq : ∀ (q : Nat) (hq : q < gs.length), q ≠ p → gs[q].ia ≠ n ∧ gs[q].ib ≠ n)
    (hpos : p + 1 < gs.length ∨ (p + 1 = gs.length ∧ a = (n + 1) + (gs.length - 2))) :
    ∃ e : Bool, ∀ x : Assign n,
      circuitOut x (restrictTrue n gs p a inv) = xor e (circuitOut (snocT x true) gs) := by
  have ha : a < (n + 1) + p := by
    have hw := hwf ⟨p, hp⟩
    simp only [List.get_eq_getElem] at hw
    rw [hgate] at hw
    exact hw.1
  have hnr := noRefVar_contract n gs p a inv hp hane huniq
  rcases hpos with h1 | ⟨h2, h3⟩
  · refine ⟨false, fun x => ?_⟩
    rw [restrictTrue, circuitOut_dropVar x true _ hnr]
    rw [circuitOut_contract_at (n + 1) gs p a inv hwf h1 ha (snocT x true)
      (passthrough_of_soleReader n gs p a inv hwf hp hgate x)]
    simp
  · refine ⟨inv, fun x => ?_⟩
    rw [restrictTrue, circuitOut_dropVar x true _ hnr]
    exact circuitOut_contract_output_at (n + 1) gs p a inv hwf h2 (by omega) h3 (snocT x true)
      (passthrough_of_soleReader n gs p a inv hwf hp hgate x)

theorem opt_liftAnd_lower (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (hc : CircuitComputes gs (liftAnd z))
    (p a : Nat) (inv : Bool) (hp : p < gs.length)
    (hgate : gs[p] = ⟨inv, a, false, n⟩) (hane : a ≠ n)
    (huniq : ∀ (q : Nat) (hq : q < gs.length), q ≠ p → gs[q].ia ≠ n ∧ gs[q].ib ≠ n)
    (hpos : p + 1 < gs.length ∨ (p + 1 = gs.length ∧ a = (n + 1) + (gs.length - 2))) :
    mz + 1 ≤ gs.length := by
  have ha : a < (n + 1) + p := by
    have hw := hwf ⟨p, hp⟩
    simp only [List.get_eq_getElem] at hw
    rw [hgate] at hw
    exact hw.1
  obtain ⟨e, he⟩ := circuitOut_restrictTrue n gs p a inv hwf hp hgate hane huniq hpos
  have hlift : ∀ x : Assign n, liftAnd z (snocT x true) = z x := by
    intro x
    rw [liftAnd, dropLast_snocT, snocT_last]
    simp
  have hcomp : CircuitComputes (restrictTrue n gs p a inv) z := by
    rcases hc with h | h
    · cases e with
      | false => exact Or.inl (fun x => by rw [he x, h (snocT x true), hlift x]; simp)
      | true => exact Or.inr (fun x => by rw [he x, h (snocT x true), hlift x]; simp)
    · cases e with
      | false => exact Or.inr (fun x => by rw [he x, h (snocT x true), hlift x]; simp)
      | true => exact Or.inl (fun x => by rw [he x, h (snocT x true), hlift x]; simp)
  have hhc : HasCircuit z (gs.length - 1) :=
    ⟨restrictTrue n gs p a inv,
     wfC_restrictTrue n gs p a inv hwf hp ha hane huniq,
     by rw [length_restrictTrue n gs p a inv hp]; exact Nat.le_refl _, hcomp⟩
  have := hz.2 _ hhc
  omega

private def rtZ : Func 2 := fun x => x 0 && x 1
private def rtGs : List Gate := [⟨false, 0, false, 1⟩, ⟨false, 3, false, 2⟩]

theorem rt_control :
    rtGs = liftCircuit 2 false [⟨false, 0, false, 1⟩]
      ∧ restrictTrue 2 rtGs 1 3 false = [⟨false, 0, false, 1⟩]
      ∧ (restrictTrue 2 rtGs 1 3 false).length + 1 = rtGs.length := by
  refine ⟨by rfl, by rfl, by rfl⟩

theorem rt_computes : ∀ x : Assign 2, circuitOut x (restrictTrue 2 rtGs 1 3 false) = rtZ x := by
  intro x
  simp [restrictTrue, rtGs, rtZ, dropVar, dropGate, dropWire, contract, contractGate,
    contractWire, circuitOut, evalGates, wireVal]

theorem dropVar_renumbers :
    dropVar 2 [⟨false, 0, false, 1⟩, ⟨false, 3, false, 3⟩]
      = [⟨false, 0, false, 1⟩, ⟨false, 2, false, 2⟩] := by rfl

#print axioms rt_control
#print axioms rt_computes
#print axioms dropVar_renumbers

#print axioms circuitOut_dropVar
#print axioms passthrough_of_soleReader
#print axioms noRefVar_contract
#print axioms circuitOut_restrictTrue
#print axioms opt_liftAnd_lower

theorem circuitOut_indep_of_unread (n : Nat) (gs : List Gate) (hno : NoRefVar n gs)
    (x : Assign n) (b b' : Bool) :
    circuitOut (snocT x b) gs = circuitOut (snocT x b') gs := by
  rw [← circuitOut_dropVar x b gs hno, ← circuitOut_dropVar x b' gs hno]

theorem exists_reader_of_liftAnd (n : Nat) (z : Func n) (gs : List Gate)
    (hz0 : z ≠ fun _ => false) (hc : CircuitComputes gs (liftAnd z)) : ¬ NoRefVar n gs := by
  intro hno
  have hlift : ∀ (x : Assign n) (b : Bool), liftAnd z (snocT x b) = (z x && b) := by
    intro x b
    rw [liftAnd, dropLast_snocT, snocT_last]
  refine hz0 (funext fun x => ?_)
  have hind := circuitOut_indep_of_unread n gs hno x true false
  rcases hc with h | h
  · rw [h (snocT x true), h (snocT x false), hlift x true, hlift x false] at hind
    simpa using hind
  · rw [h (snocT x true), h (snocT x false), hlift x true, hlift x false] at hind
    have := hind
    cases hzx : z x
    · rfl
    · rw [hzx] at this; simp at this

def twoR : List Gate := [⟨false, 0, false, 2⟩, ⟨false, 1, false, 2⟩, ⟨false, 3, false, 4⟩]

theorem twoR_computes : ∀ x : Assign 3, circuitOut x twoR = (x 0 && x 1 && x 2) := by
  intro x
  simp [twoR, circuitOut, evalGates, wireVal]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl

theorem second_reader_survives :
    contract 3 0 0 false twoR = [⟨false, 1, false, 2⟩, ⟨false, 0, false, 3⟩]
      ∧ refsWire (⟨false, 1, false, 2⟩ : Gate) 2 = true
      ∧ (contract 3 0 0 false twoR).length + 1 = twoR.length := by
  refine ⟨by rfl, by rfl, by rfl⟩

#print axioms twoR_computes
#print axioms second_reader_survives

#print axioms circuitOut_indep_of_unread
#print axioms exists_reader_of_liftAnd

def litZ : Func 1 := fun x => x 0

theorem empty_only_const (n : Nat) (f : Func n) (h : CircuitComputes [] f) :
    (∀ x, f x = false) ∨ (∀ x, f x = true) := by
  rcases h with h | h
  · refine Or.inl (fun x => ?_)
    have := h x
    simp [circuitOut, evalGates] at this
    exact this
  · refine Or.inr (fun x => ?_)
    have := h x
    simp [circuitOut, evalGates] at this
    cases hfx : f x
    · rw [hfx] at this; simp at this
    · rfl

private theorem wf_one (n : Nat) (g : Gate) (h : g.ia < n ∧ g.ib < n) : wfC n [g] := by
  intro p
  obtain ⟨i, hi⟩ := p
  simp only [List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by simpa using Nat.lt_of_lt_of_le h.1 (Nat.le_add_right n 0),
                   by simpa using Nat.lt_of_lt_of_le h.2 (Nat.le_add_right n 0)⟩

theorem litZ_needs_gate : ¬ HasCircuit litZ 0 := by
  intro ⟨gs, _, hlen, hc⟩
  have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
  rw [hnil] at hc
  rcases empty_only_const 1 litZ hc with h | h
  · have := h (fun _ => true); simp [litZ] at this
  · have := h (fun _ => false); simp [litZ] at this

theorem litZ_opt : IsOpt litZ 1 := by
  refine ⟨⟨[⟨false, 0, false, 0⟩], wf_one 1 _ ⟨by decide, by decide⟩, Nat.le_refl 1, Or.inl ?_⟩, ?_⟩
  · intro x; simp [circuitOut, evalGates, wireVal, litZ]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [hk0] at hk; exact absurd hk litZ_needs_gate
    · exact hk1

theorem liftLitZ_opt : IsOpt (liftAnd litZ) 1 := by
  refine ⟨⟨[⟨false, 0, false, 1⟩], wf_one 2 _ ⟨by decide, by decide⟩, Nat.le_refl 1, Or.inl ?_⟩, ?_⟩
  · intro x; simp [circuitOut, evalGates, wireVal, liftAnd, litZ, dropLast, Fin.last]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [hk0] at hk
      rcases hk with ⟨gs, _, hlen, hc⟩
      have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      rw [hnil] at hc
      rcases empty_only_const 2 (liftAnd litZ) hc with h | h
      · have := h (fun _ => true); simp [liftAnd, litZ, dropLast, Fin.last] at this
      · have := h (fun _ => false); simp [liftAnd, litZ, dropLast, Fin.last] at this
    · exact hk1

theorem lift_fails_on_literal :
    ¬ (∀ mz m : Nat, IsOpt litZ mz → IsOpt (liftAnd litZ) m → m = mz + 1) := by
  intro h
  have := h 1 1 litZ_opt liftLitZ_opt
  simp at this

theorem litZ_tree : IsTree litZ 0 := by
  refine ⟨⟨.var 0, Nat.le_refl 0, Or.inl ?_⟩, fun k _ => Nat.zero_le k⟩
  funext x; rfl

theorem model_asymmetric_on_literal : IsTree litZ 0 ∧ IsOpt litZ 1 := ⟨litZ_tree, litZ_opt⟩

theorem litZ_excluded_by_hgap :
    ¬ (∃ mz tz, IsOpt litZ mz ∧ IsTree litZ tz ∧ tz = mz + 1) := by
  intro ⟨mz, tz, hm, ht, hg⟩
  have h1 : mz = 1 := Nat.le_antisymm (hm.2 1 litZ_opt.1) (litZ_opt.2 mz hm.1)
  have h0 : tz = 0 := Nat.le_antisymm (ht.2 0 litZ_tree.1) (Nat.zero_le tz)
  rw [h1, h0] at hg
  simp at hg

#print axioms empty_only_const
#print axioms litZ_opt
#print axioms liftLitZ_opt
#print axioms lift_fails_on_literal
#print axioms model_asymmetric_on_literal
#print axioms litZ_excluded_by_hgap

def SliceComputes (n : Nat) (gs : List Gate) (z : Func n) : Prop :=
  ∃ c : Bool, ∀ x : Assign n, circuitOut (snocT x true) gs = xor c (z x)

theorem sliceComputes_of_liftAnd (n : Nat) (z : Func n) (gs : List Gate)
    (hc : CircuitComputes gs (liftAnd z)) : SliceComputes n gs z := by
  have hlift : ∀ x : Assign n, liftAnd z (snocT x true) = z x := by
    intro x; rw [liftAnd, dropLast_snocT, snocT_last]; simp
  rcases hc with h | h
  · exact ⟨false, fun x => by rw [h (snocT x true), hlift x]; simp⟩
  · exact ⟨true, fun x => by rw [h (snocT x true), hlift x]; simp⟩

theorem slice_trunc_lower (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (na : Bool) (j : Nat)
    (hj : j + 1 < gs.length)
    (hout : gs[gs.length - 1]'(by omega) = ⟨na, (n + 1) + j, false, n⟩)
    (hno : NoRefVar n (gs.take (j + 1)))
    (hsc : SliceComputes n gs z) :
    mz + 1 ≤ gs.length := by
  obtain ⟨c, hc⟩ := hsc
  have hlen' : (gs.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hp : gs.length - 1 < gs.length := by omega
  have hsub : (n + 1) + j - (n + 1) = j := by omega
  have hkey : ∀ x : Assign n,
      circuitOut x (dropVar n (gs.take (j + 1))) = xor (xor na c) (z x) := by
    intro x
    rw [circuitOut_dropVar x true (gs.take (j + 1)) hno]
    have h1 : circuitOut (snocT x true) (gs.take (j + 1))
        = (evalGates (snocT x true) (gs.take (j + 1))).getD j false := by
      unfold circuitOut; rw [hlen']; simp
    rw [h1, ← getD_evalGates_take (n + 1) (snocT x true) gs j (by omega)]
    have hone := getD_evalGates_eq (n + 1) (snocT x true) gs (gs.length - 1) hp hwf
    rw [hout] at hone
    have hn : wireVal (snocT x true) (evalGates (snocT x true) gs) n = true := by
      rw [wireVal_lt _ _ n (Nat.lt_succ_self n)]; simp [snocT]
    have hgj : wireVal (snocT x true) (evalGates (snocT x true) gs) ((n + 1) + j)
        = (evalGates (snocT x true) gs).getD j false := by
      rw [wireVal_ge _ _ _ (by omega), hsub]
    rw [hn, hgj] at hone
    have hcx := hc x
    unfold circuitOut at hcx
    rw [hone] at hcx
    revert hcx
    generalize (evalGates (snocT x true) gs).getD j false = G
    generalize z x = Z
    cases na <;> cases c <;> cases G <;> cases Z <;> simp
  refine Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (hz.2 (gs.length - 1) ?_) (by omega))
  refine ⟨dropVar n (gs.take (j + 1)),
    wfC_dropVar n _ (wfC_take (n + 1) gs (j + 1) hwf) hno, ?_, ?_⟩
  · rw [length_dropVar, hlen']; omega
  · cases hxc : xor na c
    · exact Or.inl (fun x => by have := hkey x; rw [hxc] at this; simpa using this)
    · exact Or.inr (fun x => by have := hkey x; rw [hxc] at this; simpa using this)

#print axioms sliceComputes_of_liftAnd
#print axioms slice_trunc_lower

def trGs : List Gate := [⟨false, 0, false, 1⟩, ⟨false, 3, false, 2⟩]

theorem trunc_control :
    NoRefVar 2 (trGs.take 1)
      ∧ trGs[trGs.length - 1]'(by decide) = ⟨false, (2 + 1) + 0, false, 2⟩
      ∧ SliceComputes 2 trGs (fun x => x 0 && x 1) := by
  refine ⟨?_, by rfl, false, fun x => ?_⟩
  · intro g hg
    have : g = ⟨false, 0, false, 1⟩ := by
      simp [trGs] at hg; exact hg
    rw [this]; exact ⟨by decide, by decide⟩
  · simp [trGs, circuitOut, evalGates, wireVal, snocT]

#print axioms trunc_control

def ReadsPos (n : Nat) (g : Gate) : Prop :=
  (g.ia = n ∧ g.na = false) ∨ (g.ib = n ∧ g.nb = false)

theorem passthrough_slice (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC (n + 1) gs) (hread : ReadsPos n gs[p]) :
    ∃ (a : Nat) (inv : Bool), a < (n + 1) + p ∧ (gs[p].ia = n → a = gs[p].ib) ∧
      ∀ x : Assign n, (evalGates (snocT x true) gs).getD p false
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a) := by
  have hwfp := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hwfp
  have hstep : ∀ x : Assign n,
      wireVal (snocT x true) (evalGates (snocT x true) gs) n = true := by
    intro x; rw [wireVal_lt _ _ n (Nat.lt_succ_self n)]; simp [snocT]
  rcases hread with ⟨hia, hna⟩ | ⟨hib, hnb⟩
  · refine ⟨gs[p].ib, gs[p].nb, hwfp.2, fun _ => rfl, fun x => ?_⟩
    rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hia, hna, hstep x]
    simp
  · refine ⟨gs[p].ia, gs[p].na, hwfp.1, ?_, fun x => ?_⟩
    · intro hia
      have : gs[p].ia = gs[p].ib := by rw [hia, hib]
      exact this
    · rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hib, hnb, hstep x]
      simp

#print axioms passthrough_slice

private theorem exists_mem_of_countP_ne_zero {α : Type} (f : α → Bool) :
    ∀ l : List α, l.countP f ≠ 0 → ∃ a, a ∈ l ∧ f a = true := by
  intro l
  induction l with
  | nil => intro h; exact absurd (by simp) h
  | cons g t ih =>
    intro h
    by_cases hg : f g = true
    · exact ⟨g, List.mem_cons_self .., hg⟩
    · rw [List.countP_cons] at h
      simp only [hg, if_false, Nat.add_zero] at h
      obtain ⟨a, ha, hfa⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

def readers (n : Nat) (gs : List Gate) : Nat := gs.countP (fun g => refsWire g n)

theorem exists_reader_below_last (n : Nat) (gs : List Gate)
    (h : readers n gs.dropLast ≠ 0) :
    ∃ (i : Nat) (hi : i + 1 < gs.length), refsWire (gs[i]'(by omega)) n = true := by
  obtain ⟨g, hg, hfg⟩ := exists_mem_of_countP_ne_zero _ _ h
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  have hlen : gs.dropLast.length = gs.length - 1 := List.length_dropLast
  rw [hlen] at hi
  have hi2 : i + 1 < gs.length := by omega
  refine ⟨i, hi2, ?_⟩
  have := List.getElem_dropLast (xs := gs) (i := i) (by rw [hlen]; omega)
  rw [← this, hgi]
  exact hfg

#print axioms exists_reader_below_last

theorem contractWire_eq_var_iff (n p a w : Nat) (hane : a ≠ n) :
    contractWire (n + 1) p a w = n ↔ w = n := by
  unfold contractWire
  by_cases h1 : w = (n + 1) + p
  · simp [h1, hane]
    omega
  · by_cases h2 : (n + 1) + p < w
    · simp [h1, h2]; omega
    · simp [h1, h2]

theorem refsWire_contractGate (n p a : Nat) (inv : Bool) (g : Gate) (hane : a ≠ n) :
    refsWire (contractGate (n + 1) p a inv g) n = refsWire g n := by
  have key : ∀ w : Nat, (contractWire (n + 1) p a w == n) = (w == n) := by
    intro w
    have hiff := contractWire_eq_var_iff n p a w hane
    by_cases hw : w = n
    · rw [hiff.mpr hw, hw]
    · have hnw : contractWire (n + 1) p a w ≠ n := fun hh => hw (hiff.mp hh)
      have l : (contractWire (n + 1) p a w == n) = false := by simp [hnw]
      have r : (w == n) = false := by simp [hw]
      rw [l, r]
  unfold refsWire contractGate
  rw [key g.ia, key g.ib]

theorem readers_contract_lt (n : Nat) (gs : List Gate) (p a : Nat) (inv : Bool)
    (hp : p < gs.length) (hane : a ≠ n) (hread : refsWire gs[p] n = true) :
    readers n (contract (n + 1) p a inv gs) + 1 ≤ readers n gs := by
  unfold readers contract
  rw [List.countP_map]
  have hfun : (fun g => refsWire (contractGate (n + 1) p a inv g) n)
      = (fun g => refsWire g n) := by
    funext g; exact refsWire_contractGate n p a inv g hane
  simp only [Function.comp_def, hfun]
  exact countP_eraseIdx_succ_le _ gs p hp (by simpa using hread)

#print axioms contractWire_eq_var_iff
#print axioms refsWire_contractGate
#print axioms readers_contract_lt

theorem noRefVar_of_readers_zero (n : Nat) (gs : List Gate) (h : readers n gs = 0) :
    NoRefVar n gs := by
  intro g hg
  have := List.countP_eq_zero.mp h g hg
  unfold refsWire at this
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this
  exact this

theorem readers_ne_zero_of_mem (n : Nat) (gs : List Gate) (g : Gate) (hg : g ∈ gs)
    (hr : refsWire g n = true) : readers n gs ≠ 0 := by
  intro h
  exact absurd hr (by simpa using List.countP_eq_zero.mp h g hg)

theorem reader_index (n : Nat) (gs : List Gate) (h : readers n gs ≠ 0) :
    ∃ (i : Nat) (hi : i < gs.length), refsWire (gs[i]'hi) n = true := by
  obtain ⟨g, hg, hfg⟩ := exists_mem_of_countP_ne_zero _ _ h
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  exact ⟨i, hi, by rw [hgi]; exact hfg⟩

theorem dropLast_readers_ne_zero (n : Nat) (gs : List Gate) (i : Nat)
    (hi : i + 1 < gs.length) (hr : refsWire (gs[i]'(by omega)) n = true) :
    readers n gs.dropLast ≠ 0 := by
  have hlen : gs.dropLast.length = gs.length - 1 := List.length_dropLast
  have hid : i < gs.dropLast.length := by rw [hlen]; omega
  refine readers_ne_zero_of_mem n gs.dropLast (gs.dropLast[i]'hid) (List.getElem_mem hid) ?_
  rw [List.getElem_dropLast (xs := gs) (i := i) hid]
  exact hr

#print axioms noRefVar_of_readers_zero
#print axioms reader_index
#print axioms dropLast_readers_ne_zero

theorem slice_trunc_lower_pt (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (inv : Bool) (j : Nat)
    (hj : j + 1 < gs.length)
    (hpt : ∀ x : Assign n, (evalGates (snocT x true) gs).getD (gs.length - 1) false
        = xor inv ((evalGates (snocT x true) gs).getD j false))
    (hno : NoRefVar n (gs.take (j + 1)))
    (hsc : SliceComputes n gs z) :
    mz + 1 ≤ gs.length := by
  obtain ⟨c, hc⟩ := hsc
  have hlen' : (gs.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hkey : ∀ x : Assign n,
      circuitOut x (dropVar n (gs.take (j + 1))) = xor (xor inv c) (z x) := by
    intro x
    rw [circuitOut_dropVar x true (gs.take (j + 1)) hno]
    have h1 : circuitOut (snocT x true) (gs.take (j + 1))
        = (evalGates (snocT x true) (gs.take (j + 1))).getD j false := by
      unfold circuitOut; rw [hlen']; simp
    rw [h1, ← getD_evalGates_take (n + 1) (snocT x true) gs j (by omega)]
    have hcx := hc x
    unfold circuitOut at hcx
    rw [hpt x] at hcx
    revert hcx
    generalize (evalGates (snocT x true) gs).getD j false = G
    generalize z x = Z
    cases inv <;> cases c <;> cases G <;> cases Z <;> simp
  refine Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (hz.2 (gs.length - 1) ?_) (by omega))
  refine ⟨dropVar n (gs.take (j + 1)),
    wfC_dropVar n _ (wfC_take (n + 1) gs (j + 1) hwf) hno, ?_, ?_⟩
  · rw [length_dropVar, hlen']; omega
  · cases hxc : xor inv c
    · exact Or.inl (fun x => by have := hkey x; rw [hxc] at this; simpa using this)
    · exact Or.inr (fun x => by have := hkey x; rw [hxc] at this; simpa using this)

#print axioms slice_trunc_lower_pt

def AllReadersPos (n : Nat) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, refsWire g n = true → ReadsPos n g

def NoBothVar (n : Nat) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, ¬(g.ia = n ∧ g.ib = n)

theorem passthrough_slice' (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC (n + 1) gs) (hread : ReadsPos n gs[p])
    (hnb : ¬(gs[p].ia = n ∧ gs[p].ib = n)) :
    ∃ (a : Nat) (inv : Bool), a < (n + 1) + p ∧ a ≠ n ∧ refsWire gs[p] a = true ∧
      ∀ x : Assign n, (evalGates (snocT x true) gs).getD p false
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a) := by
  have hwfp := hwf ⟨p, hp⟩
  simp only [List.get_eq_getElem] at hwfp
  have hstep : ∀ x : Assign n,
      wireVal (snocT x true) (evalGates (snocT x true) gs) n = true := by
    intro x; rw [wireVal_lt _ _ n (Nat.lt_succ_self n)]; simp [snocT]
  rcases hread with ⟨hia, hna⟩ | ⟨hib, hnb2⟩
  · refine ⟨gs[p].ib, gs[p].nb, hwfp.2, fun hh => hnb ⟨hia, hh⟩, by simp [refsWire],
      fun x => ?_⟩
    rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hia, hna, hstep x]
    simp
  · refine ⟨gs[p].ia, gs[p].na, hwfp.1, fun hh => hnb ⟨hh, hib⟩, by simp [refsWire],
      fun x => ?_⟩
    rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hib, hnb2, hstep x]
    simp

theorem sliceComputes_contract (n : Nat) (z : Func n) (gs : List Gate) (i a : Nat) (inv : Bool)
    (hwf : wfC (n + 1) gs) (hi : i + 1 < gs.length) (hai : a < (n + 1) + i)
    (hpt : ∀ x : Assign n, (evalGates (snocT x true) gs).getD i false
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a))
    (hsc : SliceComputes n gs z) :
    SliceComputes n (contract (n + 1) i a inv gs) z := by
  obtain ⟨c, hc⟩ := hsc
  refine ⟨c, fun x => ?_⟩
  rw [circuitOut_contract_at (n + 1) gs i a inv hwf hi hai (snocT x true) (hpt x)]
  exact hc x

private theorem contractGate_var_pol (n p a : Nat) (inv : Bool) (g : Gate) (hane : a ≠ n) :
    ((contractGate (n + 1) p a inv g).ia = n ↔ g.ia = n)
    ∧ ((contractGate (n + 1) p a inv g).ib = n ↔ g.ib = n)
    ∧ (g.ia = n → (contractGate (n + 1) p a inv g).na = g.na)
    ∧ (g.ib = n → (contractGate (n + 1) p a inv g).nb = g.nb) := by
  refine ⟨contractWire_eq_var_iff n p a g.ia hane, contractWire_eq_var_iff n p a g.ib hane,
    ?_, ?_⟩
  · intro hia
    unfold contractGate
    have : ¬ (g.ia = (n + 1) + p) := by omega
    simp [this]
  · intro hib
    unfold contractGate
    have : ¬ (g.ib = (n + 1) + p) := by omega
    simp [this]

theorem allReadersPos_contract (n : Nat) (gs : List Gate) (i a : Nat) (inv : Bool)
    (hane : a ≠ n) (hpos : AllReadersPos n gs) :
    AllReadersPos n (contract (n + 1) i a inv gs) := by
  intro g' hg' hr'
  unfold contract at hg'
  obtain ⟨g, hg, hgg⟩ := List.mem_map.mp hg'
  have hgs : g ∈ gs := List.mem_of_mem_eraseIdx hg
  have hrg : refsWire g n = true := by
    rw [← refsWire_contractGate n i a inv g hane, hgg]; exact hr'
  have hrp := hpos g hgs hrg
  obtain ⟨h1, h2, h3, h4⟩ := contractGate_var_pol n i a inv g hane
  rw [← hgg]
  rcases hrp with ⟨hia, hna⟩ | ⟨hib, hnb⟩
  · exact Or.inl ⟨h1.mpr hia, by rw [h3 hia]; exact hna⟩
  · exact Or.inr ⟨h2.mpr hib, by rw [h4 hib]; exact hnb⟩

theorem noBothVar_contract (n : Nat) (gs : List Gate) (i a : Nat) (inv : Bool)
    (hane : a ≠ n) (hboth : NoBothVar n gs) :
    NoBothVar n (contract (n + 1) i a inv gs) := by
  intro g' hg'
  unfold contract at hg'
  obtain ⟨g, hg, hgg⟩ := List.mem_map.mp hg'
  have hgs : g ∈ gs := List.mem_of_mem_eraseIdx hg
  obtain ⟨h1, h2, _, _⟩ := contractGate_var_pol n i a inv g hane
  rw [← hgg]
  intro ⟨ha, hb⟩
  exact hboth g hgs ⟨h1.mp ha, h2.mp hb⟩

#print axioms passthrough_slice'
#print axioms sliceComputes_contract
#print axioms allReadersPos_contract
#print axioms noBothVar_contract

def IsLiteral {n : Nat} (z : Func n) : Prop :=
  ∃ (i : Fin n) (b : Bool), z = fun x => xor b (x i)

theorem lower_of_no_reader (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (hno : NoRefVar n gs)
    (hsc : SliceComputes n gs z) : mz ≤ gs.length := by
  obtain ⟨c, hc⟩ := hsc
  refine hz.2 gs.length ⟨dropVar n gs, wfC_dropVar n gs hwf hno,
    by rw [length_dropVar]; exact Nat.le_refl _, ?_⟩
  cases hc' : c
  · refine Or.inl (fun x => ?_)
    rw [circuitOut_dropVar x true gs hno, hc x, hc']; simp
  · refine Or.inr (fun x => ?_)
    rw [circuitOut_dropVar x true gs hno, hc x, hc']; simp

theorem mem_dropLast_of_mem_take (gs : List Gate) (k : Nat) (hk : k + 1 ≤ gs.length)
    (g : Gate) (hg : g ∈ gs.take k) : g ∈ gs.dropLast := by
  obtain ⟨q, hq, hgq⟩ := List.getElem_of_mem hg
  have hlt : (gs.take k).length = min k gs.length := List.length_take
  have hqk : q < k := by rw [hlt] at hq; omega
  have hql : q + 1 < gs.length + 1 := by omega
  have hdl : gs.dropLast.length = gs.length - 1 := List.length_dropLast
  have hqd : q < gs.dropLast.length := by rw [hdl]; omega
  refine ?_
  have h1 : (gs.take k)[q]'hq = gs[q]'(by omega) := List.getElem_take
  have h2 : gs.dropLast[q]'hqd = gs[q]'(by omega) := List.getElem_dropLast hqd
  have : gs.dropLast[q]'hqd = g := by rw [h2, ← h1, hgq]
  rw [← this]
  exact List.getElem_mem hqd

#print axioms lower_of_no_reader
#print axioms mem_dropLast_of_mem_take

private theorem uniq_aux (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hlit : ¬ IsLiteral z) :
    ∀ (k : Nat) (gs : List Gate), gs.length ≤ k → wfC (n + 1) gs →
      SliceComputes n gs z → AllReadersPos n gs → NoBothVar n gs → readers n gs ≠ 0 →
      mz + 1 ≤ gs.length := by
  intro k
  induction k with
  | zero =>
    intro gs hlen _ _ _ _ hr
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    rw [hnil] at hr
    exact absurd (by unfold readers; simp) hr
  | succ k ih =>
    intro gs hlen hwf hsc hpos hboth hr
    by_cases hdl : readers n gs.dropLast = 0
    · obtain ⟨i, hi, hri⟩ := reader_index n gs hr
      have hlast : i + 1 = gs.length := by
        refine Classical.byContradiction (fun hne => ?_)
        exact (dropLast_readers_ne_zero n gs i (by omega) hri) hdl
      have hmem : gs[i] ∈ gs := List.getElem_mem hi
      obtain ⟨a, inv, hai, hane, href, hpt⟩ :=
        passthrough_slice' n gs i hi hwf (hpos _ hmem hri) (hboth _ hmem)
      have hieq : i = gs.length - 1 := by omega
      by_cases han : a < n
      · exfalso
        obtain ⟨c, hc⟩ := hsc
        refine hlit ⟨⟨a, han⟩, xor c inv, funext fun x => ?_⟩
        have hcx := hc x
        unfold circuitOut at hcx
        rw [← hieq, hpt x] at hcx
        have hw : wireVal (snocT x true) (evalGates (snocT x true) gs) a = x ⟨a, han⟩ := by
          rw [wireVal_lt _ _ a (by omega)]
          simp [snocT, han]
        rw [hw] at hcx
        revert hcx
        generalize x ⟨a, han⟩ = X
        generalize z x = Z
        cases inv <;> cases c <;> cases X <;> cases Z <;> simp
      · have hj : (a - (n + 1)) + 1 < gs.length := by omega
        have hptj : ∀ x : Assign n,
            (evalGates (snocT x true) gs).getD (gs.length - 1) false
              = xor inv ((evalGates (snocT x true) gs).getD (a - (n + 1)) false) := by
          intro x
          rw [← hieq, hpt x, wireVal_ge _ _ _ (by omega)]
        have hno : NoRefVar n (gs.take ((a - (n + 1)) + 1)) := by
          intro g hg
          exact noRefVar_of_readers_zero n gs.dropLast hdl g
            (mem_dropLast_of_mem_take gs _ (by omega) g hg)
        exact slice_trunc_lower_pt n z mz hz gs hwf inv (a - (n + 1)) hj hptj hno hsc
    · obtain ⟨i, hi2, hri⟩ := exists_reader_below_last n gs hdl
      have hi : i < gs.length := by omega
      have hmem : gs[i] ∈ gs := List.getElem_mem hi
      obtain ⟨a, inv, hai, hane, href, hpt⟩ :=
        passthrough_slice' n gs i hi hwf (hpos _ hmem hri) (hboth _ hmem)
      have hlen1 : (contract (n + 1) i a inv gs).length = gs.length - 1 :=
        length_contract (n + 1) i a inv gs hi
      have hwf1 := wfC_contract (n + 1) gs i a inv hwf hi hai
      have hsc1 := sliceComputes_contract n z gs i a inv hwf hi2 hai hpt hsc
      have hpos1 := allReadersPos_contract n gs i a inv hane hpos
      have hboth1 := noBothVar_contract n gs i a inv hane hboth
      by_cases hr1 : readers n (contract (n + 1) i a inv gs) = 0
      · have := lower_of_no_reader n z mz hz _ hwf1
          (noRefVar_of_readers_zero n _ hr1) hsc1
        omega
      · have := ih (contract (n + 1) i a inv gs) (by omega) hwf1 hsc1 hpos1 hboth1 hr1
        omega

#print axioms uniq_aux

theorem mem_eraseIdx_of_index_ne (gs : List Gate) (i q : Nat) (hq : q < gs.length)
    (hne : q ≠ i) : gs[q] ∈ gs.eraseIdx i := by
  rw [List.eraseIdx_eq_take_drop_succ]
  rcases Nat.lt_or_ge q i with hlt | hge
  · refine List.mem_append_left _ ?_
    have hlen : (gs.take i).length = min i gs.length := List.length_take
    have hqt : q < (gs.take i).length := by rw [hlen]; omega
    have he : (gs.take i)[q]'hqt = gs[q]'hq := List.getElem_take
    rw [← he]; exact List.getElem_mem hqt
  · obtain ⟨r, hr⟩ : ∃ r, q = (i + 1) + r := ⟨q - (i + 1), by omega⟩
    subst hr
    refine List.mem_append_right _ ?_
    have hlen : (gs.drop (i + 1)).length = gs.length - (i + 1) := List.length_drop
    have hrd : r < (gs.drop (i + 1)).length := by rw [hlen]; omega
    have he : (gs.drop (i + 1))[r]'hrd = gs[(i + 1) + r]'(by omega) := List.getElem_drop ..
    rw [← he]; exact List.getElem_mem hrd

private theorem two_readers_aux (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hlit : ¬ IsLiteral z) (gs : List Gate) (hwf : wfC (n + 1) gs)
    (hsc : SliceComputes n gs z) (hpos : AllReadersPos n gs) (hboth : NoBothVar n gs)
    (i q : Nat) (hi : i + 1 < gs.length) (hq : q < gs.length) (hqi : q ≠ i)
    (hri : refsWire (gs[i]'(by omega)) n = true) (hrq : refsWire gs[q] n = true) :
    mz + 2 ≤ gs.length := by
  have hi' : i < gs.length := by omega
  have hmem : gs[i]'hi' ∈ gs := List.getElem_mem hi'
  obtain ⟨a, inv, hai, hane, href, hpt⟩ :=
    passthrough_slice' n gs i hi' hwf (hpos _ hmem hri) (hboth _ hmem)
  have hlen1 := length_contract (n + 1) i a inv gs hi'
  have hwf1 := wfC_contract (n + 1) gs i a inv hwf hi' hai
  have hsc1 := sliceComputes_contract n z gs i a inv hwf hi hai hpt hsc
  have hpos1 := allReadersPos_contract n gs i a inv hane hpos
  have hboth1 := noBothVar_contract n gs i a inv hane hboth
  have hrne : readers n (contract (n + 1) i a inv gs) ≠ 0 := by
    refine readers_ne_zero_of_mem n _ (contractGate (n + 1) i a inv (gs[q]'hq)) ?_ ?_
    · unfold contract
      exact List.mem_map_of_mem (mem_eraseIdx_of_index_ne gs i q hq hqi)
    · rw [refsWire_contractGate n i a inv _ hane]; exact hrq
  have := uniq_aux n z mz hz hlit (contract (n + 1) i a inv gs).length
    (contract (n + 1) i a inv gs) (Nat.le_refl _) hwf1 hsc1 hpos1 hboth1 hrne
  omega

theorem uniq_reader (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hlit : ¬ IsLiteral z) (gs : List Gate) (hwf : wfC (n + 1) gs)
    (hsc : SliceComputes n gs z) (hpos : AllReadersPos n gs) (hboth : NoBothVar n gs)
    (hub : gs.length ≤ mz + 1)
    (i₁ i₂ : Nat) (h1 : i₁ < gs.length) (h2 : i₂ < gs.length) (hne : i₁ ≠ i₂)
    (hr1 : refsWire gs[i₁] n = true) (hr2 : refsWire gs[i₂] n = true) : False := by
  rcases Nat.lt_or_ge (i₁ + 1) gs.length with hlt | hge
  · have := two_readers_aux n z mz hz hlit gs hwf hsc hpos hboth i₁ i₂ hlt h2
      (fun h => hne h.symm) hr1 hr2
    omega
  · have hlt2 : i₂ + 1 < gs.length := by omega
    have := two_readers_aux n z mz hz hlit gs hwf hsc hpos hboth i₂ i₁ hlt2 h1 hne hr2 hr1
    omega

#print axioms mem_eraseIdx_of_index_ne
#print axioms uniq_reader

theorem opt_liftAnd_lower_nopos (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hz0 : z ≠ fun _ => false) (hlit : ¬ IsLiteral z)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (hc : CircuitComputes gs (liftAnd z))
    (hpos : AllReadersPos n gs) (hboth : NoBothVar n gs) :
    mz + 1 ≤ gs.length := by
  have hsc := sliceComputes_of_liftAnd n z gs hc
  have hnr : ¬ NoRefVar n gs := exists_reader_of_liftAnd n z gs hz0 hc
  have hr : readers n gs ≠ 0 := fun h => hnr (noRefVar_of_readers_zero n gs h)
  exact uniq_aux n z mz hz hlit gs.length gs (Nat.le_refl _) hwf hsc hpos hboth hr

theorem and2_not_literal : ¬ IsLiteral (fun x : Assign 2 => x 0 && x 1) := by
  intro ⟨i, b, h⟩
  have hT := congrFun h (fun _ => true)
  have h10 := congrFun h (fun j => decide (j.val = 0))
  have h01 := congrFun h (fun j => decide (j.val = 1))
  match i with
  | ⟨0, _⟩ => revert hT h10; cases b <;> simp
  | ⟨1, _⟩ => revert hT h01; cases b <;> simp

theorem lower_nopos_control :
    AllReadersPos 2 trGs ∧ NoBothVar 2 trGs
      ∧ CircuitComputes trGs (liftAnd (fun x : Assign 2 => x 0 && x 1)) := by
  refine ⟨?_, ?_, Or.inl (fun x => ?_)⟩
  · intro g hg hrg
    have hcase : g = ⟨false, 0, false, 1⟩ ∨ g = ⟨false, 3, false, 2⟩ := by
      simp [trGs] at hg; exact hg
    rcases hcase with h | h
    · rw [h] at hrg; exact absurd hrg (by decide)
    · rw [h]; exact Or.inr ⟨by decide, by decide⟩
  · intro g hg
    have : g = ⟨false, 0, false, 1⟩ ∨ g = ⟨false, 3, false, 2⟩ := by
      simp [trGs] at hg; exact hg
    rcases this with h | h <;> rw [h] <;> exact (by decide)
  · simp [trGs, circuitOut, evalGates, wireVal, liftAnd, dropLast, Fin.last]

#print axioms opt_liftAnd_lower_nopos
#print axioms and2_not_literal
#print axioms lower_nopos_control

theorem dropWire_eq_iff (n w p : Nat) (hw : w ≠ n) :
    dropWire n w = n + p ↔ w = (n + 1) + p := by
  unfold dropWire
  by_cases h : w < n
  · rw [if_pos h]
    constructor
    · intro hh
      omega
    · intro hh
      omega
  · rw [if_neg h]
    constructor
    · intro hh
      omega
    · intro hh
      omega

theorem fanOut_dropVar_needs_noRefVar :
    fanOut 0 (dropVar 0 [⟨false, 0, false, 0⟩]) 0 ≠ fanOut 1 [⟨false, 0, false, 0⟩] 0 := by
  decide

theorem fanOut_dropVar (n : Nat) (gs : List Gate) (hno : NoRefVar n gs) (p : Nat) :
    fanOut n (dropVar n gs) p = fanOut (n + 1) gs p := by
  unfold fanOut dropVar
  rw [List.countP_map]
  refine List.countP_congr (fun g hg => ?_)
  have hia := (hno g hg).1
  have hib := (hno g hg).2
  simp only [Function.comp_def, refsWire, dropGate, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro hh
    rcases hh with h1 | h1
    · exact Or.inl ((dropWire_eq_iff n g.ia p hia).mp h1)
    · exact Or.inr ((dropWire_eq_iff n g.ib p hib).mp h1)
  · intro hh
    rcases hh with h1 | h1
    · exact Or.inl ((dropWire_eq_iff n g.ia p hia).mpr h1)
    · exact Or.inr ((dropWire_eq_iff n g.ib p hib).mpr h1)

theorem numReconv_dropVar (n : Nat) (gs : List Gate) (hno : NoRefVar n gs) :
    numReconv n (dropVar n gs) = numReconv (n + 1) gs := by
  unfold numReconv
  rw [length_dropVar]
  refine List.countP_congr (fun q _ => ?_)
  simp [fanOut_dropVar n gs hno q]

theorem fanOut_take_le (n : Nat) (gs : List Gate) (k p : Nat) :
    fanOut n (gs.take k) p ≤ fanOut n gs p := by
  unfold fanOut
  have h := List.countP_append (l₁ := gs.take k) (l₂ := gs.drop k)
    (p := fun g => refsWire g (n + p))
  rw [List.take_append_drop] at h
  omega

theorem numReconv_take_le (n : Nat) (gs : List Gate) (k : Nat) :
    numReconv n (gs.take k) ≤ numReconv n gs := by
  unfold numReconv
  have h1 : (List.range (gs.take k).length).countP (fun p => decide (2 ≤ fanOut n (gs.take k) p))
      ≤ (List.range (gs.take k).length).countP (fun p => decide (2 ≤ fanOut n gs p)) := by
    refine List.countP_mono_left (fun x _ hx => ?_)
    have := fanOut_take_le n gs k x
    simp only [decide_eq_true_eq] at hx ⊢
    omega
  have hle : (gs.take k).length ≤ gs.length := by rw [List.length_take]; omega
  have h2 : (List.range (gs.take k).length).countP (fun p => decide (2 ≤ fanOut n gs p))
      ≤ (List.range gs.length).countP (fun p => decide (2 ≤ fanOut n gs p)) :=
    (List.range_sublist.mpr hle).countP_le
  omega

theorem numReconv_dropDead_le (n : Nat) (gs : List Gate) (p : Nat) (hwf : wfC n gs)
    (hp : p < gs.length) (hnc : NoConsumer n gs p) :
    numReconv n (dropDead n gs p) ≤ numReconv n gs := by
  unfold dropDead
  rw [← contract_eq_of_noConsumer n gs p (gs[p]).ia false hnc]
  refine numReconv_contract_le n gs p (gs[p]).ia false hwf hp ?_
  simp [refsWire]

#print axioms dropWire_eq_iff
#print axioms fanOut_dropVar_needs_noRefVar
#print axioms fanOut_dropVar
#print axioms numReconv_dropVar
#print axioms numReconv_take_le
#print axioms numReconv_dropDead_le

def IsConstSlice (n : Nat) (gs : List Gate) (p : Nat) (c : Bool) : Prop :=
  ∀ x : Assign n, (evalGates (snocT x true) gs).getD p false = c

theorem reader_dichotomy_slice (n : Nat) (gs : List Gate) (p : Nat) (hp : p < gs.length)
    (hwf : wfC (n + 1) gs) (hr : refsWire gs[p] n = true) :
    (∃ (a : Nat) (inv : Bool), a < (n + 1) + p ∧ a ≠ n ∧ refsWire gs[p] a = true ∧
       ∀ x : Assign n, (evalGates (snocT x true) gs).getD p false
         = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a))
    ∨ (∃ κ : Bool, IsConstSlice n gs p κ) := by
  have hstep : ∀ x : Assign n,
      wireVal (snocT x true) (evalGates (snocT x true) gs) n = true := by
    intro x; rw [wireVal_lt _ _ n (Nat.lt_succ_self n)]; simp [snocT]
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hr
  by_cases hb : gs[p].ia = n ∧ gs[p].ib = n
  · refine Or.inr ⟨(xor gs[p].na true) && (xor gs[p].nb true), fun x => ?_⟩
    rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf, hb.1, hb.2, hstep x]
  · by_cases hpos : ReadsPos n gs[p]
    · exact Or.inl (passthrough_slice' n gs p hp hwf hpos hb)
    · refine Or.inr ⟨false, fun x => ?_⟩
      rw [getD_evalGates_eq (n + 1) (snocT x true) gs p hp hwf]
      unfold ReadsPos at hpos
      rcases hr with hia | hib
      · have hna : gs[p].na = true := by
          cases h : gs[p].na
          · exact absurd (Or.inl ⟨hia, h⟩) hpos
          · rfl
        rw [hia, hna, hstep x]; simp
      · have hnb : gs[p].nb = true := by
          cases h : gs[p].nb
          · exact absurd (Or.inr ⟨hib, h⟩) hpos
          · rfl
        rw [hib, hnb, hstep x]; simp

#print axioms reader_dichotomy_slice

theorem const_consumer_gen (n : Nat) (gs : List Gate) (p r : Nat) (c : Bool)
    (hwf : wfC n gs) (hr : r < gs.length) (hrefs : refsWire gs[r] (n + p) = true) :
    (∀ x : Assign n, (evalGates x gs).getD p false = c →
        (evalGates x gs).getD r false = false)
    ∨ (∃ (a : Nat) (inv : Bool), a < n + r ∧ refsWire gs[r] a = true ∧ ∀ x : Assign n,
        (evalGates x gs).getD p false = c →
        (evalGates x gs).getD r false
          = xor inv (wireVal x (evalGates x gs) a)) := by
  have hw := hwf ⟨r, hr⟩
  simp only [List.get_eq_getElem] at hw
  have hval : ∀ x : Assign n, (evalGates x gs).getD r false
      = ((xor (gs[r]).na (wireVal x (evalGates x gs) (gs[r]).ia))
        && (xor (gs[r]).nb (wireVal x (evalGates x gs) (gs[r]).ib))) :=
    fun x => getD_evalGates_eq n x gs r hr hwf
  have hcp : ∀ x : Assign n, (evalGates x gs).getD p false = c →
      wireVal x (evalGates x gs) (n + p) = c := by
    intro x hx
    rw [wireVal_ge x (evalGates x gs) (n + p) (by omega)]
    have he : n + p - n = p := by omega
    rw [he]; exact hx
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hrefs
  rcases hrefs with hia | hib
  · by_cases hz : xor (gs[r]).na c = false
    · exact Or.inl (fun x hx => by rw [hval x, hia, hcp x hx, hz]; simp)
    · have hz' : xor (gs[r]).na c = true := by
        cases h : xor (gs[r]).na c
        · exact absurd h hz
        · rfl
      exact Or.inr ⟨(gs[r]).ib, (gs[r]).nb, hw.2, by simp [refsWire],
        fun x hx => by rw [hval x, hia, hcp x hx, hz']; simp⟩
  · by_cases hz : xor (gs[r]).nb c = false
    · exact Or.inl (fun x hx => by rw [hval x, hib, hcp x hx, hz]; simp)
    · have hz' : xor (gs[r]).nb c = true := by
        cases h : xor (gs[r]).nb c
        · exact absurd h hz
        · rfl
      exact Or.inr ⟨(gs[r]).ia, (gs[r]).na, hw.1, by simp [refsWire],
        fun x hx => by rw [hval x, hib, hcp x hx, hz']; simp⟩

theorem consumer_index (n : Nat) (gs : List Gate) (p : Nat) (hwf : wfC n gs)
    (h : fanOut n gs p ≠ 0) :
    ∃ (r : Nat) (hr : r < gs.length), p < r ∧ refsWire (gs[r]'hr) (n + p) = true := by
  obtain ⟨g, hg, hfg⟩ := exists_mem_of_countP_ne_zero _ _ h
  obtain ⟨r, hr, hgr⟩ := List.getElem_of_mem hg
  have hrefs : refsWire (gs[r]'hr) (n + p) = true := by rw [hgr]; exact hfg
  refine ⟨r, hr, ?_, hrefs⟩
  have hw := hwf ⟨r, hr⟩
  simp only [List.get_eq_getElem] at hw
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq] at hrefs
  rcases hrefs with hia | hib
  · omega
  · omega

#print axioms const_consumer_gen
#print axioms consumer_index

def SliceSmaller (n : Nat) (z : Func n) (gs : List Gate) : Prop :=
  ∃ gs1 : List Gate, gs1.length < gs.length ∧ wfC (n + 1) gs1 ∧ SliceComputes n gs1 z
    ∧ numReconv (n + 1) gs1 ≤ numReconv (n + 1) gs

private theorem const_output_absurd (n : Nat) (z : Func n) (gs : List Gate)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hsc : SliceComputes n gs z)
    (κ : Bool) (h : ∀ x : Assign n, circuitOut (snocT x true) gs = κ) : False := by
  obtain ⟨c, hc⟩ := hsc
  have key : ∀ x : Assign n, z x = xor c κ := by
    intro x
    have h1 := hc x
    rw [h x] at h1
    revert h1
    generalize z x = Z
    cases c <;> cases κ <;> cases Z <;> simp
  cases hck : xor c κ
  · exact hz0 (funext fun x => by rw [key x, hck])
  · exact hz1 (funext fun x => by rw [key x, hck])

private theorem literal_absurd (n : Nat) (z : Func n) (gs : List Gate)
    (hlit : ¬ IsLiteral z) (hsc : SliceComputes n gs z) (a : Nat) (han : a < n) (inv : Bool)
    (h : ∀ x : Assign n, circuitOut (snocT x true) gs
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a)) : False := by
  obtain ⟨c, hc⟩ := hsc
  refine hlit ⟨⟨a, han⟩, xor c inv, funext fun x => ?_⟩
  have h1 := hc x
  rw [h x] at h1
  have hw : wireVal (snocT x true) (evalGates (snocT x true) gs) a = x ⟨a, han⟩ := by
    rw [wireVal_lt _ _ a (by omega)]; simp [snocT, han]
  rw [hw] at h1
  revert h1
  generalize x ⟨a, han⟩ = X
  generalize z x = Z
  cases inv <;> cases c <;> cases X <;> cases Z <;> simp

theorem step_of_pt (n : Nat) (z : Func n) (gs : List Gate) (hwf : wfC (n + 1) gs)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z)
    (hsc : SliceComputes n gs z) (p a : Nat) (inv : Bool)
    (hp : p < gs.length) (hai : a < (n + 1) + p) (href : refsWire gs[p] a = true)
    (hpt : ∀ x : Assign n, (evalGates (snocT x true) gs).getD p false
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a)) :
    SliceSmaller n z gs := by
  rcases Nat.lt_or_ge (p + 1) gs.length with hlt | hge
  · refine ⟨contract (n + 1) p a inv gs, ?_,
      wfC_contract (n + 1) gs p a inv hwf hp hai,
      sliceComputes_contract n z gs p a inv hwf hlt hai hpt hsc,
      numReconv_contract_le (n + 1) gs p a inv hwf hp (by simpa using href)⟩
    rw [length_contract (n + 1) p a inv gs hp]; omega
  · have hlast : p + 1 = gs.length := by omega
    have hco : ∀ x : Assign n, circuitOut (snocT x true) gs
        = xor inv (wireVal (snocT x true) (evalGates (snocT x true) gs) a) := by
      intro x
      unfold circuitOut
      have : gs.length - 1 = p := by omega
      rw [this]; exact hpt x
    rcases Nat.lt_or_ge a n with han | hagen
    · exact absurd (literal_absurd n z gs hlit hsc a han inv hco) (fun h => h)
    · rcases Nat.eq_or_lt_of_le hagen with haeq | hagt
      · exfalso
        refine const_output_absurd n z gs hz0 hz1 hsc (xor inv true) (fun x => ?_)
        rw [hco x, ← haeq, wireVal_lt _ _ n (Nat.lt_succ_self n)]
        simp [snocT]
      ·
        have hn1 : n + 1 ≤ a := by omega
        obtain ⟨j, hj⟩ : ∃ j, a = (n + 1) + j := ⟨a - (n + 1), by omega⟩
        have hjl : j + 1 < gs.length := by omega
        have hlen' : (gs.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
        obtain ⟨c, hc⟩ := hsc
        refine ⟨gs.take (j + 1), by omega, wfC_take (n + 1) gs (j + 1) hwf,
          ⟨xor inv c, fun x => ?_⟩, numReconv_take_le (n + 1) gs (j + 1)⟩
        have h1 : circuitOut (snocT x true) (gs.take (j + 1))
            = (evalGates (snocT x true) (gs.take (j + 1))).getD j false := by
          unfold circuitOut; rw [hlen']; simp
        rw [h1, ← getD_evalGates_take (n + 1) (snocT x true) gs j (by omega)]
        have h2 := hco x
        rw [hj, wireVal_ge _ _ _ (by omega)] at h2
        have h3 : (n + 1) + j - (n + 1) = j := by omega
        rw [h3] at h2
        have h4 := hc x
        rw [h2] at h4
        revert h4
        generalize (evalGates (snocT x true) gs).getD j false = G
        generalize z x = Z
        cases inv <;> cases c <;> cases G <;> cases Z <;> simp

#print axioms step_of_pt

private theorem step_of_const (n : Nat) (z : Func n) (gs : List Gate) (hwf : wfC (n + 1) gs)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z)
    (hsc : SliceComputes n gs z) :
    ∀ (k p : Nat) (κ : Bool), gs.length - p ≤ k → p < gs.length →
      IsConstSlice n gs p κ → SliceSmaller n z gs := by
  intro k
  induction k with
  | zero => intro p κ hk hp _; exfalso; omega
  | succ k ih =>
    intro p κ hk hp hconst
    rcases Nat.lt_or_ge (p + 1) gs.length with hlt | hge
    · by_cases hnc : NoConsumer (n + 1) gs p
      · refine ⟨dropDead (n + 1) gs p, ?_, wfC_dropDead (n + 1) gs p hwf hp, ?_,
          numReconv_dropDead_le (n + 1) gs p hwf hp hnc⟩
        · rw [length_dropDead (n + 1) gs p hp]; omega
        · obtain ⟨c, hc⟩ := hsc
          refine ⟨c, fun x => ?_⟩
          rw [circuitOut_dropDead (n + 1) gs p hwf hlt hnc (snocT x true)]
          exact hc x
      · obtain ⟨r, hr, hpr, hrefs⟩ := consumer_index (n + 1) gs p hwf hnc
        rcases const_consumer_gen (n + 1) gs p r κ hwf hr hrefs with hcf | ⟨a, inv, hai, href, hpt⟩
        · exact ih r false (by omega) hr (fun x => hcf (snocT x true) (hconst x))
        · exact step_of_pt n z gs hwf hz0 hz1 hlit hsc r a inv hr hai href
            (fun x => hpt (snocT x true) (hconst x))
    · exfalso
      refine const_output_absurd n z gs hz0 hz1 hsc κ (fun x => ?_)
      unfold circuitOut
      have he : gs.length - 1 = p := by omega
      rw [he]; exact hconst x

theorem circuitComputes_dropVar_of_slice (n : Nat) (z : Func n) (gs : List Gate)
    (hno : NoRefVar n gs) (hsc : SliceComputes n gs z) : CircuitComputes (dropVar n gs) z := by
  obtain ⟨c, hc⟩ := hsc
  cases hcb : c with
  | false => exact Or.inl (fun x => by rw [circuitOut_dropVar x true gs hno, hc x, hcb]; simp)
  | true => exact Or.inr (fun x => by rw [circuitOut_dropVar x true gs hno, hc x, hcb]; simp)

theorem lower_no_positivity (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z) :
    ∀ (k : Nat) (gs : List Gate), gs.length ≤ k → wfC (n + 1) gs →
      SliceComputes n gs z → readers n gs ≠ 0 →
      mz + 1 ≤ gs.length
        ∧ ∃ gs' : List Gate, wfC n gs' ∧ gs'.length < gs.length ∧ CircuitComputes gs' z
            ∧ numReconv n gs' ≤ numReconv (n + 1) gs := by
  intro k
  induction k with
  | zero =>
    intro gs hlen _ _ hr
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    rw [hnil] at hr
    exact absurd (by unfold readers; simp) hr
  | succ k ih =>
    intro gs hlen hwf hsc hr
    obtain ⟨i, hi, hri⟩ := reader_index n gs hr
    have hsmall : SliceSmaller n z gs := by
      rcases reader_dichotomy_slice n gs i hi hwf hri with ⟨a, inv, hai, _, href, hpt⟩ | ⟨κ, hconst⟩
      · exact step_of_pt n z gs hwf hz0 hz1 hlit hsc i a inv hi hai href hpt
      · exact step_of_const n z gs hwf hz0 hz1 hlit hsc gs.length i κ (by omega) hi hconst
    obtain ⟨gs1, hlt1, hwf1, hsc1, hnr1⟩ := hsmall
    by_cases hr1 : readers n gs1 = 0
    · have hno1 := noRefVar_of_readers_zero n gs1 hr1
      have hcc := circuitComputes_dropVar_of_slice n z gs1 hno1 hsc1
      have hlenv : (dropVar n gs1).length = gs1.length := length_dropVar n gs1
      have hmz : mz ≤ gs1.length := by
        have h := hz.2 gs1.length ⟨dropVar n gs1, wfC_dropVar n gs1 hwf1 hno1,
          by rw [hlenv]; exact Nat.le_refl _, hcc⟩
        omega
      refine ⟨by omega, dropVar n gs1, wfC_dropVar n gs1 hwf1 hno1, by omega, hcc, ?_⟩
      rw [numReconv_dropVar n gs1 hno1]
      omega
    · obtain ⟨hle1, gs', hwf', hlen', hcc', hnrc'⟩ := ih gs1 (by omega) hwf1 hsc1 hr1
      exact ⟨by omega, gs', hwf', by omega, hcc', by omega⟩

#print axioms step_of_const
#print axioms lower_no_positivity

theorem opt_liftAnd_lower_clean (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z)
    (gs : List Gate) (hwf : wfC (n + 1) gs) (hc : CircuitComputes gs (liftAnd z)) :
    mz + 1 ≤ gs.length := by
  have hsc := sliceComputes_of_liftAnd n z gs hc
  have hnr : ¬ NoRefVar n gs := exists_reader_of_liftAnd n z gs hz0 hc
  have hr : readers n gs ≠ 0 := fun h => hnr (noRefVar_of_readers_zero n gs h)
  exact (lower_no_positivity n z mz hz hz0 hz1 hlit gs.length gs (Nat.le_refl _) hwf hsc hr).1

theorem opt_liftAnd (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z) :
    IsOpt (liftAnd z) (mz + 1) := by
  refine ⟨hasCircuit_liftAnd z mz hz0 hz1 hz.1, fun k hk => ?_⟩
  obtain ⟨gs, hwf, hlen, hc⟩ := hk
  exact Nat.le_trans (opt_liftAnd_lower_clean n z mz hz hz0 hz1 hlit gs hwf hc) hlen

#print axioms opt_liftAnd_lower_clean
#print axioms opt_liftAnd

inductive Res (n : Nat) where
  | frm : Bool → Frm n → Res n
  | const : Bool → Res n

def evalR (r : Res n) : Func n :=
  match r with
  | .frm p F => fun x => xor p (evalF F x)
  | .const c => fun _ => c

def combine (pa : Bool) (ra : Res n) (pb : Bool) (rb : Res n) : Res n :=
  match ra, rb with
  | .const ca, .const cb => .const ((xor pa ca) && (xor pb cb))
  | .const ca, .frm q B => if xor pa ca then .frm (xor pb q) B else .const false
  | .frm q A, .const cb => if xor pb cb then .frm (xor pa q) A else .const false
  | .frm q A, .frm r B => .frm false (.and (xor pa q) A (xor pb r) B)

def rs (n : Nat) : Frm (n + 1) → Res n
  | .var i => if h : i.val < n then .frm false (.var ⟨i.val, h⟩) else .const true
  | .one => .const true
  | .and pa a pb b => combine pa (rs n a) pb (rs n b)

theorem evalR_combine (pa pb : Bool) (ra rb : Res n) (x : Assign n) :
    evalR (combine pa ra pb rb) x
      = ((xor pa (evalR ra x)) && (xor pb (evalR rb x))) := by
  cases ra with
  | const ca =>
    cases rb with
    | const cb => simp [combine, evalR]
    | frm q B =>
      cases hpa : xor pa ca with
      | false => simp [combine, evalR, hpa]
      | true => simp [combine, evalR, hpa]
  | frm q A =>
    cases rb with
    | const cb =>
      cases hpb : xor pb cb with
      | false => simp [combine, evalR, hpb]
      | true => simp [combine, evalR, hpb]
    | frm r B =>
      simp only [combine, evalR, evalF]
      cases pa <;> cases pb <;> cases q <;> cases r <;>
        cases evalF A x <;> cases evalF B x <;> simp

theorem evalR_rs (φ : Frm (n + 1)) (x : Assign n) :
    evalR (rs n φ) x = evalF φ (snocT x true) := by
  induction φ with
  | var i =>
    by_cases h : i.val < n
    · simp [rs, h, evalR, evalF, snocT]
    · simp [rs, h, evalR, evalF, snocT]
  | one => simp [rs, evalR, evalF]
  | and pa a pb b iha ihb =>
    rw [rs, evalR_combine, iha, ihb]
    simp [evalF]

#print axioms evalR_combine
#print axioms evalR_rs

def usesLast (n : Nat) : Frm (n + 1) → Bool
  | .var i => decide (i.val = n)
  | .one => true
  | .and _ a _ b => usesLast n a || usesLast n b

theorem gatesF_rs_le (φ : Frm (n + 1)) :
    ∀ (p : Bool) (F : Frm n), rs n φ = .frm p F → gatesF F ≤ gatesF φ := by
  induction φ with
  | var i =>
    intro p F h
    by_cases hi : i.val < n
    · simp only [rs, dif_pos hi, Res.frm.injEq] at h
      rw [← h.2]; simp [gatesF]
    · simp only [rs, dif_neg hi] at h
      exact absurd h (by simp)
  | one => intro p F h; simp only [rs] at h; exact absurd h (by simp)
  | and pa a pb b iha ihb =>
    intro p F h
    simp only [rs] at h
    cases hra : rs n a with
    | const ca =>
      cases hrb : rs n b with
      | const cb => rw [hra, hrb] at h; simp [combine] at h
      | frm q B =>
        rw [hra, hrb] at h
        cases hpa : xor pa ca with
        | false => simp [combine, hpa] at h
        | true =>
          simp only [combine, hpa, if_pos, Res.frm.injEq] at h
          have := ihb q B hrb
          rw [← h.2]; simp [gatesF]; omega
    | frm q A =>
      cases hrb : rs n b with
      | const cb =>
        rw [hra, hrb] at h
        cases hpb : xor pb cb with
        | false => simp [combine, hpb] at h
        | true =>
          simp only [combine, hpb, if_pos, Res.frm.injEq] at h
          have := iha q A hra
          rw [← h.2]; simp [gatesF]; omega
      | frm r B =>
        rw [hra, hrb] at h
        simp only [combine, Res.frm.injEq] at h
        have h1 := iha q A hra
        have h2 := ihb r B hrb
        rw [← h.2]; simp [gatesF]; omega

theorem gatesF_rs_lt (φ : Frm (n + 1)) (hu : usesLast n φ = true) :
    ∀ (p : Bool) (F : Frm n), rs n φ = .frm p F → gatesF F + 1 ≤ gatesF φ := by
  induction φ with
  | var i =>
    intro p F h
    simp only [usesLast, decide_eq_true_eq] at hu
    have hi : ¬ i.val < n := by omega
    simp only [rs, dif_neg hi] at h
    exact absurd h (by simp)
  | one => intro p F h; simp only [rs] at h; exact absurd h (by simp)
  | and pa a pb b iha ihb =>
    intro p F h
    simp only [rs] at h
    cases hra : rs n a with
    | const ca =>
      cases hrb : rs n b with
      | const cb => rw [hra, hrb] at h; simp [combine] at h
      | frm q B =>
        rw [hra, hrb] at h
        cases hpa : xor pa ca with
        | false => simp [combine, hpa] at h
        | true =>
          simp only [combine, hpa, if_pos, Res.frm.injEq] at h
          have := gatesF_rs_le b q B hrb
          rw [← h.2]; simp [gatesF]; omega
    | frm q A =>
      cases hrb : rs n b with
      | const cb =>
        rw [hra, hrb] at h
        cases hpb : xor pb cb with
        | false => simp [combine, hpb] at h
        | true =>
          simp only [combine, hpb, if_pos, Res.frm.injEq] at h
          have := gatesF_rs_le a q A hra
          rw [← h.2]; simp [gatesF]; omega
      | frm r B =>
        rw [hra, hrb] at h
        simp only [combine, Res.frm.injEq] at h
        simp only [usesLast, Bool.or_eq_true] at hu
        rcases hu with hua | hub
        · have h1 := iha hua q A hra
          have h2 := gatesF_rs_le b r B hrb
          rw [← h.2]; simp [gatesF]; omega
        · have h1 := gatesF_rs_le a q A hra
          have h2 := ihb hub r B hrb
          rw [← h.2]; simp [gatesF]; omega

theorem indep_of_not_usesLast (φ : Frm (n + 1)) (hu : usesLast n φ = false)
    (x : Assign n) (b b' : Bool) : evalF φ (snocT x b) = evalF φ (snocT x b') := by
  induction φ with
  | var i =>
    simp only [usesLast, decide_eq_false_iff_not] at hu
    have hi : i.val < n := by omega
    simp [evalF, snocT, hi]
  | one => simp only [usesLast] at hu; exact absurd hu (by simp)
  | and pa a pb b2 iha ihb =>
    simp only [usesLast, Bool.or_eq_false_iff] at hu
    simp only [evalF, iha hu.1, ihb hu.2]

#print axioms gatesF_rs_le
#print axioms gatesF_rs_lt
#print axioms indep_of_not_usesLast

private theorem hlift_slice (z : Func n) (x : Assign n) (b : Bool) :
    liftAnd z (snocT x b) = (z x && b) := by
  rw [liftAnd, dropLast_snocT, snocT_last]

theorem tree_liftAnd_lower (n : Nat) (z : Func n) (tz : Nat) (ht : IsTree z tz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (k : Nat) (h : HasFormula (liftAnd z) k) : tz + 1 ≤ k := by
  obtain ⟨φ, hk, hc⟩ := h
  have hu : usesLast n φ = true := by
    cases hcase : usesLast n φ with
    | false =>
      exfalso
      refine hz0 (funext fun x => ?_)
      have hind := indep_of_not_usesLast φ hcase x true false
      rcases hc with hcc | hcc
      · rw [hcc] at hind
        simp only [hlift_slice] at hind
        simpa using hind
      · rw [hcc] at hind
        simp only [hlift_slice] at hind
        revert hind
        generalize z x = Z
        cases Z <;> simp
    | true => rfl
  have hslice : ∀ x : Assign n, evalR (rs n φ) x = evalF φ (snocT x true) :=
    fun x => evalR_rs φ x
  cases hr : rs n φ with
  | const c =>
    exfalso
    have hcv : ∀ x : Assign n, evalF φ (snocT x true) = c := by
      intro x; rw [← hslice x, hr]; rfl
    rcases hc with hcc | hcc
    · have key : ∀ x : Assign n, z x = c := by
        intro x
        have h1 := hcv x
        rw [hcc] at h1
        simp only [hlift_slice] at h1
        simpa using h1
      cases hcb : c with
      | false => exact hz0 (funext fun x => by rw [key x, hcb])
      | true => exact hz1 (funext fun x => by rw [key x, hcb])
    · have key : ∀ x : Assign n, z x = !c := by
        intro x
        have h1 := hcv x
        rw [hcc] at h1
        simp only [hlift_slice] at h1
        revert h1
        generalize z x = Z
        cases Z <;> cases c <;> simp
      cases hcb : c with
      | false => exact hz1 (funext fun x => by rw [key x, hcb]; simp)
      | true => exact hz0 (funext fun x => by rw [key x, hcb]; simp)
  | frm p F =>
    have hsize := gatesF_rs_lt φ hu p F hr
    have hev : ∀ x : Assign n, xor p (evalF F x) = evalF φ (snocT x true) := by
      intro x; rw [← hslice x, hr]; rfl
    have hFz : FormulaComputes F z := by
      rcases hc with hcc | hcc
      · cases hp : p with
        | false =>
          refine Or.inl (funext fun x => ?_)
          have h1 := hev x
          rw [hcc] at h1
          simp only [hlift_slice] at h1
          rw [hp] at h1
          simpa using h1
        | true =>
          refine Or.inr (funext fun x => ?_)
          have h1 := hev x
          rw [hcc] at h1
          simp only [hlift_slice] at h1
          rw [hp] at h1
          revert h1
          generalize evalF F x = Y
          generalize z x = Z
          cases Y <;> cases Z <;> simp
      · cases hp : p with
        | false =>
          refine Or.inr (funext fun x => ?_)
          have h1 := hev x
          rw [hcc] at h1
          simp only [hlift_slice] at h1
          rw [hp] at h1
          simpa using h1
        | true =>
          refine Or.inl (funext fun x => ?_)
          have h1 := hev x
          rw [hcc] at h1
          simp only [hlift_slice] at h1
          rw [hp] at h1
          revert h1
          generalize evalF F x = Y
          generalize z x = Z
          cases Y <;> cases Z <;> simp
    have := ht.2 (gatesF F) ⟨F, Nat.le_refl _, hFz⟩
    omega

theorem tree_liftAnd (n : Nat) (z : Func n) (tz : Nat) (ht : IsTree z tz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) :
    IsTree (liftAnd z) (tz + 1) :=
  ⟨hasFormula_liftAnd z tz ht.1, fun k hk => tree_liftAnd_lower n z tz ht hz0 hz1 k hk⟩

#print axioms tree_liftAnd_lower
#print axioms tree_liftAnd

private theorem literal_nonconst (z : Func n) (i : Fin n) (b : Bool)
    (hzb : z = fun x => xor b (x i)) :
    z (fun j => if j = i then true else false) = !b
    ∧ z (fun j => if j = i then false else true) = b := by
  refine ⟨?_, ?_⟩ <;> rw [hzb] <;> simp

theorem not_literal_of_gap (z : Func n) (mz tz : Nat) (hopt : IsOpt z mz) (htree : IsTree z tz)
    (hgap : tz = mz + 1) : ¬ IsLiteral z := by
  intro ⟨i, b, hzb⟩
  obtain ⟨h1, h0⟩ := literal_nonconst z i b hzb
  have ht0 : HasFormula z 0 := by
    refine ⟨.var i, Nat.le_refl _, ?_⟩
    cases hb : b with
    | false => exact Or.inl (funext fun x => by rw [hzb, hb]; simp [evalF])
    | true => exact Or.inr (funext fun x => by rw [hzb, hb]; simp [evalF])
  have htz : tz = 0 := Nat.le_antisymm (htree.2 0 ht0) (Nat.zero_le _)
  have hnc : ¬ HasCircuit z 0 := by
    intro ⟨gs, _, hlen, hcc⟩
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    rw [hnil] at hcc
    rcases empty_only_const n z hcc with h | h
    · have e1 := h (fun j => if j = i then true else false)
      have e0 := h (fun j => if j = i then false else true)
      rw [h1] at e1; rw [h0] at e0
      cases b <;> simp_all
    · have e1 := h (fun j => if j = i then true else false)
      have e0 := h (fun j => if j = i then false else true)
      rw [h1] at e1; rw [h0] at e0
      cases b <;> simp_all
  have hc1 : HasCircuit z 1 := by
    refine ⟨[⟨b, i.val, b, i.val⟩], wf_one n _ ⟨i.isLt, i.isLt⟩, Nat.le_refl _,
      Or.inl (fun x => ?_)⟩
    simp [circuitOut, evalGates, wireVal, i.isLt, hzb]
  have hmz1 : mz ≤ 1 := hopt.2 1 hc1
  have hmz0 : mz ≠ 0 := by
    intro h0'
    rw [h0'] at hopt
    exact hnc hopt.1
  omega

theorem forcedMulti_liftAnd (n : Nat) (z : Func n) (mz : Nat) (hz : IsOpt z mz)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true) (hlit : ¬ IsLiteral z)
    (hfm : ForcedMulti z) : ForcedMulti (liftAnd z) := by
  refine ⟨mz + 1, opt_liftAnd n z mz hz hz0 hz1 hlit, fun gs hwf hlen hc => ?_⟩
  obtain ⟨mz', hz', hfm'⟩ := hfm
  have hmzeq : mz' = mz := Nat.le_antisymm (hz'.2 mz hz.1) (hz.2 mz' hz'.1)
  have hsc := sliceComputes_of_liftAnd n z gs hc
  have hnr : ¬ NoRefVar n gs := exists_reader_of_liftAnd n z gs hz0 hc
  have hrne : readers n gs ≠ 0 := fun h => hnr (noRefVar_of_readers_zero n gs h)
  obtain ⟨_, gs', hwf', hlen', hcc', hnrc'⟩ :=
    lower_no_positivity n z mz hz hz0 hz1 hlit gs.length gs (Nat.le_refl _) hwf hsc hrne
  have hge : mz ≤ gs'.length := hz.2 gs'.length ⟨gs', hwf', Nat.le_refl _, hcc'⟩
  have heq : gs'.length = mz' := by omega
  have h2 := hfm' gs' hwf' heq hcc'
  omega

#print axioms forcedMulti_liftAnd

theorem lift_three (z : Func n) (mz tz : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (hopt : IsOpt z mz) (htree : IsTree z tz) (hgap : tz = mz + 1) :
    IsOpt (liftAnd z) (mz + 1) ∧ IsTree (liftAnd z) (tz + 1) ∧ Gap (liftAnd z) 1 := by
  have hlit := not_literal_of_gap z mz tz hopt htree hgap
  have ho := opt_liftAnd n z mz hopt hz0 hz1 hlit
  have ht := tree_liftAnd n z tz htree hz0 hz1
  exact ⟨ho, ht, mz + 1, tz + 1, ho, ht, by omega⟩

#print axioms not_literal_of_gap
#print axioms lift_three

theorem lift_lemma (z : Func n) (mz tz : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (hopt : IsOpt z mz) (htree : IsTree z tz) (hgap : tz = mz + 1)
    (hfm : ForcedMulti z) :
    IsOpt (liftAnd z) (mz + 1) ∧ IsTree (liftAnd z) (tz + 1) ∧
      Gap (liftAnd z) 1 ∧ ForcedMulti (liftAnd z) := by
  have hlit := not_literal_of_gap z mz tz hopt htree hgap
  obtain ⟨h1, h2, h3⟩ := lift_three z mz tz hz0 hz1 hopt htree hgap
  exact ⟨h1, h2, h3, forcedMulti_liftAnd n z mz hopt hz0 hz1 hlit hfm⟩

#print axioms lift_three
#print axioms forcedMulti_liftAnd
#print axioms lift_lemma

theorem evalGates_flip_of_unread (n : Nat) (i : Fin n)
    (gs : List Gate) (hno : ∀ g ∈ gs, g.ia ≠ i.val ∧ g.ib ≠ i.val) (x : Assign n) :
    evalGates x gs = evalGates (flipAt x i) gs := by
  have hw : ∀ (V : Array Bool) (w : Nat), w ≠ i.val →
      wireVal x V w = wireVal (flipAt x i) V w := by
    intro V w hwi
    unfold wireVal
    by_cases h : w < n
    · rw [dif_pos h, dif_pos h]
      unfold flipAt
      have : (⟨w, h⟩ : Fin n) ≠ i := fun hh => hwi (congrArg Fin.val hh)
      simp [this]
    · rw [dif_neg h, dif_neg h]
  have key : ∀ (l : List Gate), (∀ g ∈ l, g.ia ≠ i.val ∧ g.ib ≠ i.val) →
      ∀ V : Array Bool, l.foldl (gstep x) V = l.foldl (gstep (flipAt x i)) V := by
    intro l
    induction l with
    | nil => intro _ V; rfl
    | cons g t ih =>
      intro hl V
      have hg := hl g (List.mem_cons_self ..)
      have hstep : gstep x V g = gstep (flipAt x i) V g := by
        unfold gstep
        rw [hw V g.ia hg.1, hw V g.ib hg.2]
      simp only [List.foldl_cons, hstep]
      exact ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) _
  rw [evalGates_foldl, evalGates_foldl]
  exact key gs hno #[]

theorem exists_reader_of_dependsOn (n : Nat) (f : Func n) (gs : List Gate) (i : Fin n)
    (hdep : dependsOn f i) (hc : CircuitComputes gs f) :
    ¬ (∀ g ∈ gs, g.ia ≠ i.val ∧ g.ib ≠ i.val) := by
  intro hno
  obtain ⟨x, hx⟩ := hdep
  have hco : circuitOut x gs = circuitOut (flipAt x i) gs := by
    unfold circuitOut
    rw [evalGates_flip_of_unread n i gs hno x]
  rcases hc with h | h
  · rw [h x, h (flipAt x i)] at hco
    exact hx hco
  · rw [h x, h (flipAt x i)] at hco
    exact hx (by
      revert hco
      generalize f x = A
      generalize f (flipAt x i) = B
      cases A <;> cases B <;> simp)

#print axioms evalGates_flip_of_unread
#print axioms exists_reader_of_dependsOn

def edgesToWire (gs : List Gate) (w : Nat) : Nat := (gs.map (fun g => edgesTo g w)).sum

theorem edgesToWire_gate (n : Nat) (gs : List Gate) (p : Nat) :
    edgesToWire gs (n + p) = fanOutEdges n gs p := rfl

private theorem sum_map_zero {α : Type} (A : α → Nat) (h : ∀ x, A x = 0) :
    ∀ l : List α, (l.map A).sum = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, h a, ih]

private theorem sum_map_add {α : Type} (A B : α → Nat) :
    ∀ l : List α, (l.map (fun x => A x + B x)).sum = (l.map A).sum + (l.map B).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem countP_range_eq_one (a : Nat) : ∀ W : Nat, a < W →
    (List.range W).countP (fun w => a == w) = 1 := by
  intro W
  induction W with
  | zero => intro h; exact absurd h (by omega)
  | succ W ih =>
    intro h
    rw [List.range_succ, List.countP_append]
    by_cases hlt : a < W
    · rw [ih hlt]
      have : ((List.range W).countP (fun w => a == w)) = 1 := ih hlt
      simp only [List.countP_cons, List.countP_nil]
      have hne : ¬ (a == W) = true := by simp; omega
      simp [hne]
    · have haw : a = W := by omega
      have hz : (List.range W).countP (fun w => a == w) = 0 := by
        refine List.countP_eq_zero.mpr (fun x hx => ?_)
        have := List.mem_range.mp hx
        simp only [beq_iff_eq]
        omega
      rw [hz, haw]
      simp [List.countP_cons]

private theorem sum_ite_eq_one (a W : Nat) (h : a < W) :
    ((List.range W).map (fun w => if a == w then 1 else 0)).sum = 1 := by
  rw [sum_map_ite_eq_countP (fun w => a == w) (List.range W)]
  exact countP_range_eq_one a W h

theorem sum_edgesToWire (W : Nat) : ∀ gs : List Gate,
    (∀ g ∈ gs, g.ia < W ∧ g.ib < W) →
    ((List.range W).map (edgesToWire gs)).sum = 2 * gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro _
    rw [sum_map_zero (edgesToWire []) (fun w => by simp [edgesToWire]) (List.range W)]
    simp
  | cons g t ih =>
    intro hl
    have hg := hl g (List.mem_cons_self ..)
    have hsplit : ∀ w, edgesToWire (g :: t) w = edgesTo g w + edgesToWire t w := by
      intro w; simp [edgesToWire]
    have hone : ((List.range W).map (fun w => edgesTo g w)).sum = 2 := by
      have := sum_map_add (fun w => if g.ia == w then 1 else 0)
        (fun w => if g.ib == w then 1 else 0) (List.range W)
      simp only [edgesTo]
      rw [this, sum_ite_eq_one g.ia W hg.1, sum_ite_eq_one g.ib W hg.2]
    have hrest := ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
    calc ((List.range W).map (edgesToWire (g :: t))).sum
        = ((List.range W).map (fun w => edgesTo g w + edgesToWire t w)).sum := by
          congr 1
      _ = ((List.range W).map (fun w => edgesTo g w)).sum
            + ((List.range W).map (edgesToWire t)).sum :=
          sum_map_add _ _ (List.range W)
      _ = 2 * (g :: t).length := by rw [hone, hrest]; simp only [List.length_cons]; omega

#print axioms sum_edgesToWire

private theorem edges_zero_forall (w : Nat) : ∀ gs : List Gate,
    edgesToWire gs w = 0 → ∀ g ∈ gs, edgesTo g w = 0 := by
  intro gs
  induction gs with
  | nil => intro _ g hg; cases hg
  | cons a t ih =>
    intro h g hg
    have h' : edgesTo a w + edgesToWire t w = 0 := by
      simpa [edgesToWire] using h
    rcases List.mem_cons.mp hg with h1 | h2
    · subst h1; omega
    · exact ih (by omega) g h2

theorem edges_pos_of_dependsOn (n : Nat) (f : Func n) (gs : List Gate) (i : Fin n)
    (hdep : dependsOn f i) (hc : CircuitComputes gs f) : 1 ≤ edgesToWire gs i.val := by
  rcases Nat.eq_zero_or_pos (edgesToWire gs i.val) with h | h
  · exfalso
    refine exists_reader_of_dependsOn n f gs i hdep hc ?_
    intro g hg
    have h0 := edges_zero_forall i.val gs h g hg
    unfold edgesTo at h0
    refine ⟨fun hh => ?_, fun hh => ?_⟩ <;> simp [hh] at h0
  · exact h

theorem edges_pos_of_nondead (n : Nat) (f : Func n) (gs : List Gate) (m : Nat)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (p : Nat) (hp : p + 1 < gs.length) : 1 ≤ edgesToWire gs (n + p) := by
  rcases Nat.eq_zero_or_pos (edgesToWire gs (n + p)) with h | h
  · exfalso
    refine opt_no_dead_gate n f gs m hwf hopt hlen hc p hp ?_
    unfold NoConsumer fanOut
    refine List.countP_eq_zero.mpr (fun g hg => ?_)
    have h0 := edges_zero_forall (n + p) gs h g hg
    unfold edgesTo at h0
    unfold refsWire
    have h1 : (g.ia == n + p) = false := by
      rcases Bool.eq_false_or_eq_true (g.ia == n + p) with hb | hb
      · simp [hb] at h0
      · exact hb
    have h2 : (g.ib == n + p) = false := by
      rcases Bool.eq_false_or_eq_true (g.ib == n + p) with hb | hb
      · simp [hb] at h0
      · exact hb
    simp [h1, h2]
  · exact h

private theorem sum_map_le_mem {α : Type} (A B : α → Nat) : ∀ l : List α,
    (∀ x ∈ l, A x ≤ B x) → (l.map A).sum ≤ (l.map B).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private theorem sum_map_one (W : Nat) :
    ((List.range W).map (fun _ => 1)).sum = W := by
  induction W with
  | zero => simp
  | succ W ih => rw [List.range_succ]; simp only [List.map_append, List.sum_append]; simp [ih]

private theorem sum_model (W out w0 : Nat) (hout : out < W) (hw0 : w0 < W) :
    ((List.range W).map
        (fun w => (if out == w then 0 else 1) + (if w0 == w then 1 else 0))).sum = W := by
  have key : ∀ w,
      ((if out == w then 0 else 1) + (if w0 == w then 1 else 0)) + (if out == w then 1 else 0)
        = 1 + (if w0 == w then 1 else 0) := by
    intro w
    by_cases h : out == w
    · simp [h]; omega
    · simp [h]
  have hA := sum_map_add
      (fun w => (if out == w then 0 else 1) + (if w0 == w then 1 else 0))
      (fun w => if out == w then 1 else 0) (List.range W)
  have hB := sum_map_add (fun _ : Nat => 1) (fun w => if w0 == w then 1 else 0) (List.range W)
  have hcong : ((List.range W).map
      (fun w => ((if out == w then 0 else 1) + (if w0 == w then 1 else 0))
        + (if out == w then 1 else 0))).sum
      = ((List.range W).map (fun w => 1 + (if w0 == w then 1 else 0))).sum := by
    congr 1
    exact List.map_congr_left (fun w _ => key w)
  rw [hA, sum_ite_eq_one out W hout] at hcong
  rw [hB, sum_map_one W, sum_ite_eq_one w0 W hw0] at hcong
  omega

private theorem sum_map_zero_mem {α : Type} (A : α → Nat) : ∀ l : List α,
    (∀ x ∈ l, A x = 0) → (l.map A).sum = 0 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem edges_last_eq_zero (n : Nat) (gs : List Gate) (hwf : wfC n gs) :
    edgesToWire gs (n + (gs.length - 1)) = 0 := by
  have h := fanOut_last_eq_zero n gs hwf
  rw [fanOut, List.countP_eq_zero] at h
  refine sum_map_zero_mem (fun g => edgesTo g (n + (gs.length - 1))) gs ?_
  intro g hg
  have hr := h g hg
  simp only [refsWire, Bool.or_eq_true, beq_iff_eq, not_or] at hr
  unfold edgesTo
  simp [hr.1, hr.2]

theorem threshold_count (n : Nat) (f : Func n) (m : Nat)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (gs : List Gate) (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hm : 0 < m) (w0 : Nat) (hw0 : w0 < n + m)
    (hshare : 2 ≤ edgesToWire gs w0) :
    n ≤ m := by

  have hw0ne : w0 ≠ n + (m - 1) := by
    intro he
    have hz := edges_last_eq_zero n gs hwf
    rw [hlen] at hz
    rw [he] at hshare
    omega
  have hbound : ∀ g ∈ gs, g.ia < n + m ∧ g.ib < n + m := by
    intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have := hwf ⟨k, hk⟩
    simp only [List.get_eq_getElem] at this
    rw [hkg] at this
    omega
  have hsum : ((List.range (n + m)).map (edgesToWire gs)).sum = 2 * m := by
    have h := sum_edgesToWire (n + m) gs hbound
    rw [hlen] at h; exact h
  have hpt : ∀ w ∈ List.range (n + m),
      ((if (n + (m - 1)) == w then 0 else 1) + (if w0 == w then 1 else 0))
        ≤ edgesToWire gs w := by
    intro w hw
    have hwlt : w < n + m := List.mem_range.mp hw
    by_cases hout : (n + (m - 1)) == w
    · by_cases hz : w0 == w
      · exfalso; simp only [beq_iff_eq] at hout hz; omega
      · simp [hout, hz]
    · have hne : w ≠ n + (m - 1) := by simp only [beq_iff_eq] at hout; omega
      have h1 : 1 ≤ edgesToWire gs w := by
        by_cases hlt : w < n
        · exact edges_pos_of_dependsOn n f gs ⟨w, hlt⟩ (hess ⟨w, hlt⟩) hc
        · obtain ⟨p, hp⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
          subst hp
          exact edges_pos_of_nondead n f gs m hwf hopt hlen hc p (by omega)
      by_cases hz : w0 == w
      · have : w0 = w := by simp only [beq_iff_eq] at hz; exact hz
        subst this
        simp [hout]
        omega
      · simp [hout, hz]; omega
  have hge := sum_map_le_mem
      (fun w => (if (n + (m - 1)) == w then 0 else 1) + (if w0 == w then 1 else 0))
      (edgesToWire gs) (List.range (n + m)) hpt
  rw [sum_model (n + m) (n + (m - 1)) w0 (by omega) hw0] at hge
  omega

theorem threshold_of_sharing_free (n : Nat) (f : Func n) (m t : Nat)
    (hopt : IsOpt f m) (htree : IsTree f t) (hgap : t - m = 1)
    (hess : ∀ i : Fin n, dependsOn f i)
    (hsf : ∀ gs : List Gate, wfC n gs → gs.length = m → CircuitComputes gs f →
      (∀ w, w < n + m → edgesToWire gs w ≤ 1) → HasFormula f m) :
    n ≤ m := by
  obtain ⟨gs, hwf, hle, hc⟩ := hopt.1
  have hlen : gs.length = m := Nat.le_antisymm hle (hopt.2 gs.length ⟨gs, hwf, Nat.le_refl _, hc⟩)
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hgs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · exfalso
      obtain ⟨x, hx⟩ := hess ⟨0, hn⟩
      rcases empty_only_const n f hc with hcf | hcf
      · rw [hcf x, hcf (flipAt x ⟨0, hn⟩)] at hx; exact hx rfl
      · rw [hcf x, hcf (flipAt x ⟨0, hn⟩)] at hx; exact hx rfl
  · by_cases hall : ∀ w, w < n + m → edgesToWire gs w ≤ 1
    · exfalso
      have := htree.2 m (hsf gs hwf hlen hc hall)
      omega
    · obtain ⟨w0, hw0lt, hw0ge⟩ : ∃ w0, w0 < n + m ∧ 2 ≤ edgesToWire gs w0 := by
        rcases Classical.not_forall.mp hall with ⟨w0, hw0⟩
        rcases Classical.not_imp.mp hw0 with ⟨h1, h2⟩
        exact ⟨w0, h1, by omega⟩
      exact threshold_count n f m hopt hess gs hwf hlen hc hm w0 hw0lt hw0ge

#print axioms threshold_count
#print axioms threshold_of_sharing_free

private theorem sum_model_one (W out : Nat) (hout : out < W) :
    ((List.range W).map (fun w => if out == w then 0 else 1)).sum + 1 = W := by
  have key : ∀ w, (if out == w then 0 else 1) + (if out == w then 1 else 0) = 1 := by
    intro w; by_cases h : out == w <;> simp [h]
  have hA := sum_map_add (fun w => if out == w then 0 else 1)
      (fun w => if out == w then 1 else 0) (List.range W)
  have hcong : ((List.range W).map
      (fun w => (if out == w then 0 else 1) + (if out == w then 1 else 0))).sum
      = ((List.range W).map (fun _ => 1)).sum := by
    congr 1
    exact List.map_congr_left (fun w _ => key w)
  rw [hA, sum_ite_eq_one out W hout] at hcong
  rw [sum_map_one W] at hcong
  omega

theorem sharing_free_exact (n : Nat) (f : Func n) (m : Nat)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (gs : List Gate) (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hsf : ∀ w, w < n + m → edgesToWire gs w ≤ 1) :
    ∀ w, w < n + m → w ≠ n + (m - 1) → edgesToWire gs w = 1 := by
  intro w hwlt hne
  have h1 : 1 ≤ edgesToWire gs w := by
    by_cases hlt : w < n
    · exact edges_pos_of_dependsOn n f gs ⟨w, hlt⟩ (hess ⟨w, hlt⟩) hc
    · obtain ⟨p, hp⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      subst hp
      exact edges_pos_of_nondead n f gs m hwf hopt hlen hc p (by omega)
  have h2 := hsf w hwlt
  omega

theorem sharing_free_size (n : Nat) (f : Func n) (m : Nat)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (gs : List Gate) (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hm : 0 < m) (hsf : ∀ w, w < n + m → edgesToWire gs w ≤ 1) :
    m + 1 = n := by
  have hbound : ∀ g ∈ gs, g.ia < n + m ∧ g.ib < n + m := by
    intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have := hwf ⟨k, hk⟩
    simp only [List.get_eq_getElem] at this
    rw [hkg] at this
    omega
  have hsum : ((List.range (n + m)).map (edgesToWire gs)).sum = 2 * m := by
    have h := sum_edgesToWire (n + m) gs hbound
    rw [hlen] at h; exact h

  have hpt : ∀ w ∈ List.range (n + m),
      edgesToWire gs w = (if (n + (m - 1)) == w then 0 else 1) := by
    intro w hw
    have hwlt : w < n + m := List.mem_range.mp hw
    by_cases hout : (n + (m - 1)) == w
    · have he : w = n + (m - 1) := by simp only [beq_iff_eq] at hout; omega
      have hz := edges_last_eq_zero n gs hwf
      rw [hlen] at hz
      simp only [hout, if_true]
      rw [he]; exact hz
    · have hne : w ≠ n + (m - 1) := by simp only [beq_iff_eq] at hout; omega
      have h1 := sharing_free_exact n f m hopt hess gs hwf hlen hc hsf w hwlt hne
      have h2 := hsf w hwlt
      have hb : ((n + (m - 1)) == w) = false := by
        simp only [beq_eq_false_iff_ne]; omega
      rw [hb]
      simp only [Bool.false_eq_true, if_false]
      omega
  have heq : ((List.range (n + m)).map (edgesToWire gs)).sum
      = ((List.range (n + m)).map (fun w => if (n + (m - 1)) == w then 0 else 1)).sum := by
    congr 1
    exact List.map_congr_left hpt
  have hone := sum_model_one (n + m) (n + (m - 1)) (by omega)
  omega

#print axioms sharing_free_exact
#print axioms sharing_free_size

def wireFrm (n : Nat) (gs : List Gate) : Nat → Nat → Frm n
  | 0, _ => .one
  | k + 1, w =>
    if h : w < n then .var ⟨w, h⟩
    else
      match gs[w - n]? with
      | none => .one
      | some g => .and g.na (wireFrm n gs k g.ia) g.nb (wireFrm n gs k g.ib)

def wireCost (n : Nat) (gs : List Gate) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, w =>
    if w < n then 0
    else
      match gs[w - n]? with
      | none => 0
      | some g => 1 + wireCost n gs k g.ia + wireCost n gs k g.ib

theorem gatesF_wireFrm (n : Nat) (gs : List Gate) :
    ∀ k w, gatesF (wireFrm n gs k w) = wireCost n gs k w := by
  intro k
  induction k with
  | zero => intro w; simp [wireFrm, wireCost, gatesF]
  | succ k ih =>
    intro w
    by_cases h : w < n
    · simp [wireFrm, wireCost, h, gatesF]
    · simp only [wireFrm, wireCost, h, dif_neg, if_neg]
      cases hg : gs[w - n]? with
      | none => simp [hg, gatesF]
      | some g => simp [hg, gatesF, ih]

private def cfGs : List Gate := [⟨false, 0, false, 1⟩, ⟨true, 2, false, 0⟩]

theorem wireFrm_control :
    wireFrm 2 cfGs 4 3
        = .and true (.and false (.var 0) false (.var 1)) false (.var 0)
      ∧ wireCost 2 cfGs 4 3 = 2
      ∧ (∀ x : Assign 2, evalF (wireFrm 2 cfGs 4 3) x = circuitOut x cfGs) := by
  refine ⟨by rfl, by rfl, ?_⟩
  intro x
  simp [cfGs, wireFrm, evalF, circuitOut, evalGates, wireVal]

#print axioms gatesF_wireFrm
#print axioms wireFrm_control

theorem evalF_wireFrm (n : Nat) (x : Assign n) (gs : List Gate) (hwf : wfC n gs) :
    ∀ k w, w < k → w < n + gs.length →
      evalF (wireFrm n gs k w) x = wireVal x (evalGates x gs) w := by
  intro k
  induction k with
  | zero => intro w hk; exact absurd hk (by omega)
  | succ k ih =>
    intro w hk hlt
    by_cases h : w < n
    · simp only [wireFrm, h, dif_pos, evalF]
      rw [wireVal]
      simp [h]
    · have hp : w - n < gs.length := by omega
      have hget : gs[w - n]? = some gs[w - n] := List.getElem?_eq_getElem hp
      have hwn : w = n + (w - n) := by omega
      have hw := hwf ⟨w - n, hp⟩
      simp only [List.get_eq_getElem] at hw
      have hia : gs[w - n].ia < k := by omega
      have hib : gs[w - n].ib < k := by omega
      have hial : gs[w - n].ia < n + gs.length := by omega
      have hibl : gs[w - n].ib < n + gs.length := by omega
      have hshape : wireFrm n gs (k + 1) w
          = .and gs[w - n].na (wireFrm n gs k gs[w - n].ia)
                 gs[w - n].nb (wireFrm n gs k gs[w - n].ib) := by
        simp only [wireFrm]
        rw [dif_neg h, hget]
      rw [hshape]
      simp only [evalF]
      rw [ih _ hia hial, ih _ hib hibl, wireVal_ge x (evalGates x gs) w h]
      exact (getD_evalGates_eq n x gs (w - n) hp hwf).symm

#print axioms evalF_wireFrm

theorem formulaComputes_wireFrm (n : Nat) (f : Func n) (m : Nat) (gs : List Gate)
    (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f) (hm : 0 < m) :
    FormulaComputes (wireFrm n gs (n + m) (n + (m - 1))) f := by
  have hout : ∀ x : Assign n,
      evalF (wireFrm n gs (n + m) (n + (m - 1))) x = circuitOut x gs := by
    intro x
    rw [evalF_wireFrm n x gs hwf (n + m) (n + (m - 1)) (by omega) (by omega)]
    rw [wireVal_ge x (evalGates x gs) (n + (m - 1)) (by omega)]
    unfold circuitOut
    rw [show n + (m - 1) - n = m - 1 from by omega, show gs.length - 1 = m - 1 from by omega]
  rcases hc with h | h
  · exact Or.inl (funext fun x => by rw [hout x, h x])
  · exact Or.inr (funext fun x => by rw [hout x, h x])

#print axioms formulaComputes_wireFrm

theorem wireCost_dropLast (n : Nat) (gs : List Gate) (hwf : wfC n gs) :
    ∀ k w, w < n + gs.length - 1 → wireCost n gs k w = wireCost n gs.dropLast k w := by
  intro k
  induction k with
  | zero => intro w _; simp [wireCost]
  | succ k ih =>
    intro w hw
    by_cases h : w < n
    · simp only [wireCost, if_pos h]
    · have hlt : w - n < gs.length - 1 := by omega
      have hd : gs.dropLast[w - n]? = gs[w - n]? := by
        rw [List.getElem?_dropLast]
        simp [hlt]
      simp only [wireCost, if_neg h, hd]
      cases hg : gs[w - n]? with
      | none => simp only [hg]
      | some g =>
        have hp : w - n < gs.length := by omega
        have hgg : gs[w - n] = g := by
          have := List.getElem?_eq_getElem hp
          rw [hg] at this
          exact (Option.some_inj.mp this.symm)
        have hwfp := hwf ⟨w - n, hp⟩
        simp only [List.get_eq_getElem, hgg] at hwfp
        simp only [hg]
        rw [ih g.ia (by omega), ih g.ib (by omega)]

#print axioms wireCost_dropLast

private theorem wireCost_fuel (n : Nat) (gs : List Gate) (hwf : wfC n gs) :
    ∀ B w k k', w ≤ B → w < k → w < k' →
      wireCost n gs k w = wireCost n gs k' w := by
  intro B
  induction B with
  | zero =>
    intro w k k' hwB hk hk'
    obtain ⟨a, ha⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, k' = b + 1 := ⟨k' - 1, by omega⟩
    subst ha; subst hb
    by_cases h : w < n
    · simp only [wireCost, if_pos h]
    · have hw0 : w = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hw0; subst hn0
      cases hg : gs[0 - 0]? with
      | none => simp only [wireCost, if_neg h, hg]
      | some g =>
        exfalso
        obtain ⟨hp, hgg⟩ := List.getElem?_eq_some_iff.mp hg
        have hp0 : (0:Nat) < gs.length := by simpa using hp
        have := hwf ⟨0 - 0, hp⟩
        simp only [List.get_eq_getElem, hgg] at this
        omega
  | succ B ih =>
    intro w k k' hwB hk hk'
    obtain ⟨a, ha⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, k' = b + 1 := ⟨k' - 1, by omega⟩
    subst ha; subst hb
    by_cases h : w < n
    · simp only [wireCost, if_pos h]
    · simp only [wireCost, if_neg h]
      cases hg : gs[w - n]? with
      | none => simp only [hg]
      | some g =>
        obtain ⟨hp, hgg⟩ := List.getElem?_eq_some_iff.mp hg
        have hwfp := hwf ⟨w - n, hp⟩
        simp only [List.get_eq_getElem, hgg] at hwfp
        simp only [hg]
        rw [ih g.ia a b (by omega) (by omega) (by omega),
            ih g.ib a b (by omega) (by omega) (by omega)]

private theorem wfC_concat_left (n : Nat) (gs : List Gate) (g : Gate)
    (h : wfC n (gs ++ [g])) : wfC n gs := by
  intro p
  have hp : p.val < (gs ++ [g]).length := by
    have := p.isLt; simp; omega
  have h2 := h ⟨p.val, hp⟩
  simp only [List.get_eq_getElem] at h2 ⊢
  rw [List.getElem_append_left p.isLt] at h2
  exact h2

private theorem sum_map_erase (f : Nat → Nat) (a : Nat) : ∀ R : List Nat, a ∈ R →
    (R.map f).sum = f a + ((R.erase a).map f).sum := by
  intro R
  induction R with
  | nil => intro h; cases h
  | cons b t ih =>
    intro h
    by_cases hb : b = a
    · subst hb
      simp [List.erase_cons]
    · have hat : a ∈ t := by
        rcases List.mem_cons.mp h with h1 | h2
        · exact absurd h1.symm hb
        · exact h2
      have hbf : (b == a) = false := by simp [hb]
      rw [List.erase_cons, hbf]
      simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons, ih hat]
      omega

private theorem edgesToWire_concat (gs : List Gate) (g : Gate) (w : Nat) :
    edgesToWire (gs ++ [g]) w = edgesToWire gs w + edgesTo g w := by
  unfold edgesToWire
  simp [List.map_append]

private theorem wireCost_of_nil (n k : Nat) : ∀ r, r < n → wireCost n [] k r = 0 := by
  intro r hr
  cases k with
  | zero => simp [wireCost]
  | succ k => simp [wireCost, hr]

private theorem costList_aux (n k : Nat) : ∀ L : Nat, ∀ gs : List Gate, gs.length ≤ L →
    ∀ R : List Nat, wfC n gs →
    (∀ w, w < n + gs.length → w < k) →
    (∀ p, p < gs.length → edgesToWire gs (n + p) + R.count (n + p) = 1) →
    (∀ r ∈ R, r < n + gs.length) →
    (R.map (wireCost n gs k)).sum = gs.length := by
  intro L
  induction L with
  | zero =>
    intro gs hL R _ _ _ hRlt
    have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hgs
    rw [sum_map_zero_mem (wireCost n [] k) R
      (fun r hr => wireCost_of_nil n k r (by simpa using hRlt r hr))]
    simp
  | succ L ih =>
    intro gs hL R hwf hk hinv hRlt
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil
      rw [sum_map_zero_mem (wireCost n [] k) R
        (fun r hr => wireCost_of_nil n k r (by simpa using hRlt r hr))]
      simp
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hlen : (gs' ++ [g]).length = gs'.length + 1 := by simp
      have hdl : (gs' ++ [g]).dropLast = gs' := List.dropLast_concat

      have htop : edgesToWire (gs' ++ [g]) (n + gs'.length) = 0 := by
        have h := edges_last_eq_zero n (gs' ++ [g]) hwf
        rw [hlen] at h
        simpa using h

      have hcnt : R.count (n + gs'.length) = 1 := by
        have h := hinv gs'.length (by omega)
        omega
      have hmemW : (n + gs'.length) ∈ R := List.count_pos_iff.mp (by omega)

      have hgidx : (gs' ++ [g])[gs'.length]'(by omega) = g := by
        rw [List.getElem_append_right (by omega)]
        simp
      have hwfm := hwf ⟨gs'.length, by omega⟩
      simp only [List.get_eq_getElem, hgidx] at hwfm

      have hkW : n + gs'.length < k := hk _ (by omega)
      obtain ⟨a, ha⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩

      have hgetW : (gs' ++ [g])[n + gs'.length - n]? = some g := by
        rw [show n + gs'.length - n = gs'.length from by omega]
        exact List.getElem?_eq_some_iff.mpr ⟨by omega, hgidx⟩

      have hunf : wireCost n (gs' ++ [g]) (a + 1) (n + gs'.length)
          = 1 + wireCost n (gs' ++ [g]) a g.ia + wireCost n (gs' ++ [g]) a g.ib := by
        simp only [wireCost, if_neg (show ¬ (n + gs'.length < n) from by omega), hgetW]
      have htopcost : wireCost n (gs' ++ [g]) k (n + gs'.length)
          = 1 + wireCost n gs' k g.ia + wireCost n gs' k g.ib := by
        rw [ha, hunf,
            wireCost_fuel n (gs' ++ [g]) hwf (n + gs'.length) g.ia a (a + 1)
              (by omega) (by omega) (by omega),
            wireCost_fuel n (gs' ++ [g]) hwf (n + gs'.length) g.ib a (a + 1)
              (by omega) (by omega) (by omega),
            wireCost_dropLast n (gs' ++ [g]) hwf (a + 1) g.ia (by simp; omega),
            wireCost_dropLast n (gs' ++ [g]) hwf (a + 1) g.ib (by simp; omega), hdl]

      have hnotmem : (n + gs'.length) ∉ R.erase (n + gs'.length) := by
        intro hmem
        have := List.count_pos_iff.mpr hmem
        rw [List.count_erase] at this
        simp [hcnt] at this
      have hEraseLt : ∀ r ∈ R.erase (n + gs'.length), r < n + gs'.length := by
        intro r hr
        have hrR : r ∈ R := List.mem_of_mem_erase hr
        have h1 := hRlt r hrR
        rw [hlen] at h1
        have hne : r ≠ n + gs'.length := by
          intro he; subst he; exact hnotmem hr
        omega

      have hcong : ((R.erase (n + gs'.length)).map (wireCost n (gs' ++ [g]) k)).sum
          = ((R.erase (n + gs'.length)).map (wireCost n gs' k)).sum := by
        congr 1
        refine List.map_congr_left (fun r hr => ?_)
        rw [wireCost_dropLast n (gs' ++ [g]) hwf k r (by simp; exact hEraseLt r hr), hdl]

      have hIH := ih gs' (by omega) (R.erase (n + gs'.length) ++ [g.ia, g.ib])
        (wfC_concat_left n gs' g hwf)
        (fun w hwlt => hk w (by rw [hlen]; omega))
        (fun p hp => by
          have hI := hinv p (by rw [hlen]; omega)
          rw [edgesToWire_concat] at hI
          rw [List.count_append, List.count_erase]
          have hWne : ((n + gs'.length) == n + p) = false := by
            simp only [beq_eq_false_iff_ne]; omega
          rw [hWne]
          have hcnt2 : List.count (n + p) [g.ia, g.ib] = edgesTo g (n + p) := by
            unfold edgesTo
            simp only [List.count_cons, List.count_nil]
            omega
          rw [hcnt2]
          simp only [Bool.false_eq_true, if_false, Nat.sub_zero]
          omega)
        (fun r hr => by
          rcases List.mem_append.mp hr with h1 | h2
          · exact hEraseLt r h1
          · rcases List.mem_cons.mp h2 with he | he2
            · subst he; omega
            · rcases List.mem_cons.mp he2 with he3 | he4
              · subst he3; omega
              · cases he4)
      rw [List.map_append, List.sum_append] at hIH
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hIH
      rw [sum_map_erase (wireCost n (gs' ++ [g]) k) (n + gs'.length) R hmemW, htopcost, hcong, hlen]
      omega

#print axioms sum_map_erase
#print axioms edgesToWire_concat

theorem wireCost_eq (n : Nat) (f : Func n) (m : Nat) (gs : List Gate)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f) (hm : 0 < m)
    (hsf : ∀ w, w < n + m → edgesToWire gs w ≤ 1) :
    wireCost n gs (n + m) (n + (m - 1)) = m := by
  have hexact := sharing_free_exact n f m hopt hess gs hwf hlen hc hsf
  have hzero : edgesToWire gs (n + (m - 1)) = 0 := by
    have h := edges_last_eq_zero n gs hwf
    rw [hlen] at h; exact h
  have hmain := costList_aux n (n + m) gs.length gs (Nat.le_refl _) [n + (m - 1)] hwf
    (fun w hw => by omega)
    (fun p hp => by
      simp only [List.count_singleton]
      by_cases he : p = m - 1
      · subst he
        have hb : ((n + (m - 1)) == n + (m - 1)) = true := by simp
        rw [hb, hzero]
        simp
      · have hne : n + p ≠ n + (m - 1) := by omega
        have hb : ((n + (m - 1)) == n + p) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        rw [hb, hexact (n + p) (by omega) hne]
        simp)
    (fun r hr => by
      rcases List.mem_cons.mp hr with he | he2
      · subst he; omega
      · cases he2)
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hmain
  omega

#print axioms costList_aux
#print axioms wireCost_eq

theorem wireCost_le (n : Nat) (f : Func n) (m : Nat) (gs : List Gate)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f) (hm : 0 < m)
    (hsf : ∀ w, w < n + m → edgesToWire gs w ≤ 1) :
    wireCost n gs (n + m) (n + (m - 1)) ≤ m := by
  rw [wireCost_eq n f m gs hopt hess hwf hlen hc hm hsf]
  omega

theorem sharing_free_is_tree (n : Nat) (f : Func n) (m : Nat) (gs : List Gate)
    (hopt : IsOpt f m) (hess : ∀ i : Fin n, dependsOn f i)
    (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hsf : ∀ w, w < n + m → edgesToWire gs w ≤ 1) :
    HasFormula f m := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hgs

    rcases empty_only_const n f hc with hcf | hcf
    · exact ⟨.one, by simp [gatesF], Or.inr (funext fun x => by simp [evalF, hcf x])⟩
    · exact ⟨.one, by simp [gatesF], Or.inl (funext fun x => by simp [evalF, hcf x])⟩
  · refine ⟨wireFrm n gs (n + m) (n + (m - 1)), ?_, ?_⟩
    · rw [gatesF_wireFrm]
      exact wireCost_le n f m gs hopt hess hwf hlen hc hm hsf
    · exact formulaComputes_wireFrm n f m gs hwf hlen hc hm

theorem threshold (f : Func n) (m t : Nat)
    (hopt : IsOpt f m) (htree : IsTree f t)
    (hgap : t - m = 1)
    (hess : ∀ i : Fin n, dependsOn f i) :
    n ≤ m :=
  threshold_of_sharing_free n f m t hopt htree hgap hess
    (fun gs hwf hlen hc hall => sharing_free_is_tree n f m gs hopt hess hwf hlen hc hall)

#print axioms threshold

theorem input_wire_metrics_differ :
    CircuitComputes [⟨false, 0, false, 0⟩] litZ
      ∧ edgesToWire [⟨false, 0, false, 0⟩] 0 = 2
      ∧ ([⟨false, 0, false, 0⟩] : List Gate).countP (fun g => refsWire g 0) = 1 := by
  refine ⟨Or.inl (fun x => ?_), by decide, by decide⟩
  simp [circuitOut, evalGates, wireVal, litZ]

theorem leaf_duplication_is_free (n : Nat) (i : Fin n) :
    gatesF (Frm.and false (.var i) false (.var i)) = 1 ∧ gatesF ((.var i) : Frm n) = 0 := by
  refine ⟨?_, ?_⟩ <;> simp [gatesF]

#print axioms input_wire_metrics_differ
#print axioms leaf_duplication_is_free

def negF (f : Func n) : Func n := fun x => !(f x)

theorem negF_negF (f : Func n) : negF (negF f) = f := by
  funext x; simp [negF]

theorem negF_ne_false (f : Func n) (h : f ≠ fun _ => true) : negF f ≠ fun _ => false := by
  intro hc
  apply h
  funext x
  have := congrFun hc x
  simp [negF] at this
  simp [this]

theorem negF_ne_true (f : Func n) (h : f ≠ fun _ => false) : negF f ≠ fun _ => true := by
  intro hc
  apply h
  funext x
  have := congrFun hc x
  simp [negF] at this
  simp [this]

theorem circuitComputes_negF (gs : List Gate) (f : Func n) :
    CircuitComputes gs (negF f) ↔ CircuitComputes gs f := by
  constructor
  · rintro (h | h)
    · exact Or.inr (fun x => h x)
    · refine Or.inl (fun x => ?_)
      have hx := h x
      simp only [negF, Bool.not_not] at hx
      exact hx
  · rintro (h | h)
    · refine Or.inr (fun x => ?_)
      rw [h x]
      simp [negF]
    · exact Or.inl (fun x => h x)

theorem hasCircuit_negF (f : Func n) (k : Nat) : HasCircuit (negF f) k ↔ HasCircuit f k := by
  constructor <;> rintro ⟨gs, hwf, hlen, hc⟩ <;> exact ⟨gs, hwf, hlen, by
    first
      | exact (circuitComputes_negF gs f).mp hc
      | exact (circuitComputes_negF gs f).mpr hc⟩

theorem isOpt_negF (f : Func n) (m : Nat) : IsOpt (negF f) m ↔ IsOpt f m := by
  constructor
  · exact fun h => ⟨(hasCircuit_negF f m).mp h.1, fun k hk => h.2 k ((hasCircuit_negF f k).mpr hk)⟩
  · exact fun h => ⟨(hasCircuit_negF f m).mpr h.1, fun k hk => h.2 k ((hasCircuit_negF f k).mp hk)⟩

theorem formulaComputes_negF (φ : Frm n) (f : Func n) :
    FormulaComputes φ (negF f) ↔ FormulaComputes φ f := by
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · refine Or.inl ?_
      rw [h]; funext x; simp [negF]
  · rintro (h | h)
    · refine Or.inr ?_
      rw [h]; funext x; simp [negF]
    · exact Or.inl h

theorem hasFormula_negF (f : Func n) (k : Nat) : HasFormula (negF f) k ↔ HasFormula f k := by
  constructor <;> rintro ⟨φ, hlen, hc⟩ <;> exact ⟨φ, hlen, by
    first
      | exact (formulaComputes_negF φ f).mp hc
      | exact (formulaComputes_negF φ f).mpr hc⟩

theorem isTree_negF (f : Func n) (t : Nat) : IsTree (negF f) t ↔ IsTree f t := by
  constructor
  · exact fun h => ⟨(hasFormula_negF f t).mp h.1, fun k hk => h.2 k ((hasFormula_negF f k).mpr hk)⟩
  · exact fun h => ⟨(hasFormula_negF f t).mpr h.1, fun k hk => h.2 k ((hasFormula_negF f k).mp hk)⟩

theorem forcedMulti_negF (f : Func n) : ForcedMulti (negF f) ↔ ForcedMulti f := by
  constructor
  · rintro ⟨m, hopt, hall⟩
    exact ⟨m, (isOpt_negF f m).mp hopt,
      fun gs hwf hlen hc => hall gs hwf hlen ((circuitComputes_negF gs f).mpr hc)⟩
  · rintro ⟨m, hopt, hall⟩
    exact ⟨m, (isOpt_negF f m).mpr hopt,
      fun gs hwf hlen hc => hall gs hwf hlen ((circuitComputes_negF gs f).mp hc)⟩

theorem gap_negF (f : Func n) (g : Nat) : Gap (negF f) g ↔ Gap f g := by
  constructor
  · rintro ⟨m, t, ho, ht, he⟩
    exact ⟨m, t, (isOpt_negF f m).mp ho, (isTree_negF f t).mp ht, he⟩
  · rintro ⟨m, t, ho, ht, he⟩
    exact ⟨m, t, (isOpt_negF f m).mpr ho, (isTree_negF f t).mpr ht, he⟩

def negLast (x : Assign (n + 1)) : Assign (n + 1) :=
  fun i => if i = Fin.last n then !x i else x i

private theorem castSucc_ne_last (i : Fin n) : (i.castSucc : Fin (n + 1)) ≠ Fin.last n := by
  intro hc
  have h := congrArg Fin.val hc
  simp at h
  omega

private theorem mk_n_eq_last (h : n < n + 1) : (⟨n, h⟩ : Fin (n + 1)) = Fin.last n := by
  apply Fin.ext; simp

theorem negLast_negLast (x : Assign (n + 1)) : negLast (negLast x) = x := by
  funext i
  by_cases h : i = Fin.last n <;> simp [negLast, h]

theorem dropLast_negLast (x : Assign (n + 1)) : dropLast (negLast x) = dropLast x := by
  funext i
  simp only [dropLast, negLast, if_neg (castSucc_ne_last i)]

theorem wireVal_negLast_ne (x : Assign (n + 1)) (V : Array Bool) (w : Nat) (h : w ≠ n) :
    wireVal (negLast x) V w = wireVal x V w := by
  by_cases hlt : w < n + 1
  · simp only [wireVal, dif_pos hlt]
    show negLast x ⟨w, hlt⟩ = x ⟨w, hlt⟩
    have hne : (⟨w, hlt⟩ : Fin (n + 1)) ≠ Fin.last n := by
      intro hc
      have hv := congrArg Fin.val hc
      simp at hv
      omega
    simp [negLast, hne]
  · simp only [wireVal, dif_neg hlt]

theorem wireVal_negLast_eq (x : Assign (n + 1)) (V : Array Bool) :
    wireVal (negLast x) V n = !(wireVal x V n) := by
  have hlt : n < n + 1 := by omega
  simp only [wireVal, dif_pos hlt]
  show negLast x ⟨n, hlt⟩ = !(x ⟨n, hlt⟩)
  simp [negLast, mk_n_eq_last hlt]

def negWire (w : Nat) (g : Gate) : Gate :=
  ⟨if g.ia = w then !g.na else g.na, g.ia, if g.ib = w then !g.nb else g.nb, g.ib⟩

def negIn (w : Nat) (gs : List Gate) : List Gate := gs.map (negWire w)

theorem negWire_negWire (w : Nat) (g : Gate) : negWire w (negWire w g) = g := by
  obtain ⟨na, ia, nb, ib⟩ := g
  simp only [negWire]
  by_cases ha : ia = w <;> by_cases hb : ib = w <;> simp [ha, hb]

theorem negIn_negIn (w : Nat) (gs : List Gate) : negIn w (negIn w gs) = gs := by
  simp only [negIn, List.map_map]
  rw [show (negWire w ∘ negWire w) = (fun g => negWire w (negWire w g)) from rfl,
    List.map_congr_left (fun g _ => negWire_negWire w g)]
  simp

theorem length_negIn (w : Nat) (gs : List Gate) : (negIn w gs).length = gs.length := by
  simp [negIn]

theorem refsWire_negWire (w v : Nat) (g : Gate) : refsWire (negWire w g) v = refsWire g v := by
  simp [refsWire, negWire]

theorem fanOut_negIn (w : Nat) (gs : List Gate) (p : Nat) :
    fanOut n (negIn w gs) p = fanOut n gs p := by
  simp only [fanOut, negIn]
  rw [List.countP_map]
  apply List.countP_congr
  intro g _
  simp [refsWire_negWire]

theorem numReconv_negIn (w : Nat) (gs : List Gate) :
    numReconv n (negIn w gs) = numReconv n gs := by
  simp only [numReconv, length_negIn]
  apply List.countP_congr
  intro p _
  rw [fanOut_negIn]

theorem wfC_negIn (w : Nat) (gs : List Gate) (hwf : wfC n gs) : wfC n (negIn w gs) := by
  intro p
  have hp : p.val < gs.length := by
    have h := p.isLt; simp only [length_negIn] at h; exact h
  have h := hwf ⟨p.val, hp⟩
  rw [List.get_eq_getElem] at h ⊢
  have hg : (negIn w gs)[p.val] = negWire w gs[p.val] := by
    simp only [negIn]; rw [List.getElem_map]
  rw [hg]
  exact ⟨h.1, h.2⟩

private theorem evalGates_snoc {k : Nat} (x : Assign k) (gs : List Gate) (g : Gate) :
    evalGates x (gs ++ [g]) = gstep x (evalGates x gs) g := by
  rw [evalGates_foldl, List.foldl_append, evalGates_foldl]
  simp

private theorem evalGates_negIn_aux : ∀ (L : Nat) (gs : List Gate) (x : Assign (n + 1)),
    gs.length ≤ L → evalGates x (negIn n gs) = evalGates (negLast x) gs := by
  intro L
  induction L with
  | zero =>
    intro gs x hL
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; rfl
  | succ L ih =>
    intro gs x hL
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil; rfl
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hL' : gs'.length ≤ L := by simp at hL; omega
      have hmap : negIn n (gs' ++ [g]) = negIn n gs' ++ [negWire n g] := by simp [negIn]
      rw [hmap, evalGates_snoc, evalGates_snoc, ih gs' x hL', gstep, gstep, negWire]
      have hedge : ∀ (na : Bool) (ia : Nat),
          xor (if ia = n then !na else na) (wireVal x (evalGates (negLast x) gs') ia)
            = xor na (wireVal (negLast x) (evalGates (negLast x) gs') ia) := by
        intro na ia
        by_cases h : ia = n
        · subst h
          rw [if_pos rfl, wireVal_negLast_eq]
          cases na <;> cases (wireVal x (evalGates (negLast x) gs') ia) <;> rfl
        · rw [if_neg h, wireVal_negLast_ne x _ ia h]
      rw [hedge, hedge]

theorem evalGates_negIn (gs : List Gate) (x : Assign (n + 1)) :
    evalGates x (negIn n gs) = evalGates (negLast x) gs :=
  evalGates_negIn_aux gs.length gs x (Nat.le_refl _)

theorem circuitOut_negIn (gs : List Gate) (x : Assign (n + 1)) :
    circuitOut x (negIn n gs) = circuitOut (negLast x) gs := by
  rw [circuitOut, circuitOut, evalGates_negIn, length_negIn]

def cnl (f : Func (n + 1)) : Func (n + 1) := fun x => f (negLast x)

theorem cnl_cnl (f : Func (n + 1)) : cnl (cnl f) = f := by
  funext x; simp [cnl, negLast_negLast]

theorem circuitComputes_negIn (gs : List Gate) (f : Func (n + 1)) (hc : CircuitComputes gs f) :
    CircuitComputes (negIn n gs) (cnl f) := by
  rcases hc with h | h
  · exact Or.inl (fun x => by rw [circuitOut_negIn]; exact h (negLast x))
  · exact Or.inr (fun x => by rw [circuitOut_negIn]; exact h (negLast x))

theorem hasCircuit_cnl (f : Func (n + 1)) (k : Nat) : HasCircuit (cnl f) k ↔ HasCircuit f k := by
  constructor
  · rintro ⟨gs, hwf, hlen, hc⟩
    refine ⟨negIn n gs, wfC_negIn n gs hwf, by rw [length_negIn]; exact hlen, ?_⟩
    have h := circuitComputes_negIn gs (cnl f) hc
    rw [cnl_cnl] at h
    exact h
  · rintro ⟨gs, hwf, hlen, hc⟩
    exact ⟨negIn n gs, wfC_negIn n gs hwf, by rw [length_negIn]; exact hlen,
      circuitComputes_negIn gs f hc⟩

theorem isOpt_cnl (f : Func (n + 1)) (m : Nat) : IsOpt (cnl f) m ↔ IsOpt f m := by
  constructor
  · exact fun h => ⟨(hasCircuit_cnl f m).mp h.1, fun k hk => h.2 k ((hasCircuit_cnl f k).mpr hk)⟩
  · exact fun h => ⟨(hasCircuit_cnl f m).mpr h.1, fun k hk => h.2 k ((hasCircuit_cnl f k).mp hk)⟩

theorem forcedMulti_cnl (f : Func (n + 1)) : ForcedMulti (cnl f) ↔ ForcedMulti f := by
  constructor
  · rintro ⟨m, hopt, hall⟩
    refine ⟨m, (isOpt_cnl f m).mp hopt, fun gs hwf hlen hc => ?_⟩
    have h := hall (negIn n gs) (wfC_negIn n gs hwf) (by rw [length_negIn]; exact hlen)
      (circuitComputes_negIn gs f hc)
    rw [numReconv_negIn] at h
    exact h
  · rintro ⟨m, hopt, hall⟩
    refine ⟨m, (isOpt_cnl f m).mpr hopt, fun gs hwf hlen hc => ?_⟩
    have hc' : CircuitComputes (negIn n gs) (cnl (cnl f)) := circuitComputes_negIn gs (cnl f) hc
    rw [cnl_cnl] at hc'
    have h := hall (negIn n gs) (wfC_negIn n gs hwf) (by rw [length_negIn]; exact hlen) hc'
    rw [numReconv_negIn] at h
    exact h

def negFrmL : Frm (n + 1) → Frm (n + 1) × Bool
  | .var i => (.var i, decide (i = Fin.last n))
  | .one => (.one, false)
  | .and pa a pb b =>
      (.and (xor pa (negFrmL a).2) (negFrmL a).1 (xor pb (negFrmL b).2) (negFrmL b).1, false)

theorem gatesF_negFrmL : ∀ φ : Frm (n + 1), gatesF (negFrmL φ).1 = gatesF φ := by
  intro φ
  induction φ with
  | var i => rfl
  | one => rfl
  | and pa a pb b iha ihb => simp only [negFrmL, gatesF, iha, ihb]

theorem evalF_negFrmL : ∀ (φ : Frm (n + 1)) (x : Assign (n + 1)),
    evalF (negFrmL φ).1 x = xor (negFrmL φ).2 (evalF φ (negLast x)) := by
  intro φ
  induction φ with
  | var i =>
    intro x
    by_cases h : i = Fin.last n
    · subst h
      simp [negFrmL, evalF, negLast]
    · simp [negFrmL, evalF, negLast, h]
  | one => intro x; simp [negFrmL, evalF]
  | and pa a pb b iha ihb =>
    intro x
    simp only [negFrmL, evalF, iha x, ihb x]
    cases (negFrmL a).2 <;> cases (negFrmL b).2 <;> cases pa <;> cases pb <;> simp

theorem hasFormula_cnl (f : Func (n + 1)) (k : Nat) : HasFormula (cnl f) k ↔ HasFormula f k := by
  have key : ∀ (g : Func (n + 1)) (j : Nat), HasFormula g j → HasFormula (cnl g) j := by
    rintro g j ⟨φ, hlen, hc⟩
    refine ⟨(negFrmL φ).1, by rw [gatesF_negFrmL]; exact hlen, ?_⟩
    have hev : evalF (negFrmL φ).1 = fun x => xor (negFrmL φ).2 (evalF φ (negLast x)) := by
      funext x; exact evalF_negFrmL φ x
    rcases hc with h | h
    · cases hb : (negFrmL φ).2
      · refine Or.inl ?_
        rw [hev]; funext x; rw [hb, h]; simp [cnl]
      · refine Or.inr ?_
        rw [hev]; funext x; rw [hb, h]; simp [cnl]
    · cases hb : (negFrmL φ).2
      · refine Or.inr ?_
        rw [hev]; funext x; rw [hb, h]; simp [cnl]
      · refine Or.inl ?_
        rw [hev]; funext x; rw [hb, h]; simp [cnl]
  constructor
  · intro h
    have h2 := key (cnl f) k h
    rw [cnl_cnl] at h2
    exact h2
  · exact key f k

theorem isTree_cnl (f : Func (n + 1)) (t : Nat) : IsTree (cnl f) t ↔ IsTree f t := by
  constructor
  · exact fun h => ⟨(hasFormula_cnl f t).mp h.1, fun k hk => h.2 k ((hasFormula_cnl f k).mpr hk)⟩
  · exact fun h => ⟨(hasFormula_cnl f t).mpr h.1, fun k hk => h.2 k ((hasFormula_cnl f k).mp hk)⟩

theorem gap_cnl (f : Func (n + 1)) (g : Nat) : Gap (cnl f) g ↔ Gap f g := by
  constructor
  · rintro ⟨m, t, ho, ht, he⟩
    exact ⟨m, t, (isOpt_cnl f m).mp ho, (isTree_cnl f t).mp ht, he⟩
  · rintro ⟨m, t, ho, ht, he⟩
    exact ⟨m, t, (isOpt_cnl f m).mpr ho, (isTree_cnl f t).mpr ht, he⟩

theorem liftOr_eq (z : Func n) : liftOr z = negF (cnl (liftAnd (negF z))) := by
  funext x
  have hl : negLast x (Fin.last n) = !(x (Fin.last n)) := by simp [negLast]
  simp only [liftOr, negF, cnl, liftAnd, dropLast_negLast, hl]
  cases z (dropLast x) <;> cases x (Fin.last n) <;> simp

theorem lift_lemma_or (z : Func n) (mz tz : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (hopt : IsOpt z mz) (htree : IsTree z tz) (hgap : tz = mz + 1)
    (hfm : ForcedMulti z) :
    IsOpt (liftOr z) (mz + 1) ∧ IsTree (liftOr z) (tz + 1) ∧
      Gap (liftOr z) 1 ∧ ForcedMulti (liftOr z) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ :=
    lift_lemma (negF z) mz tz (negF_ne_false z hz1) (negF_ne_true z hz0)
      ((isOpt_negF z mz).mpr hopt) ((isTree_negF z tz).mpr htree) hgap
      ((forcedMulti_negF z).mpr hfm)
  rw [liftOr_eq]
  refine ⟨(isOpt_negF _ _).mpr ((isOpt_cnl _ _).mpr ha1),
    (isTree_negF _ _).mpr ((isTree_cnl _ _).mpr ha2),
    (gap_negF _ _).mpr ((gap_cnl _ _).mpr ha3),
    (forcedMulti_negF _).mpr ((forcedMulti_cnl _).mpr ha4)⟩

theorem lift_lemma_both (z : Func n) (mz tz : Nat)
    (hz0 : z ≠ fun _ => false) (hz1 : z ≠ fun _ => true)
    (hopt : IsOpt z mz) (htree : IsTree z tz) (hgap : tz = mz + 1)
    (hfm : ForcedMulti z) :
    (IsOpt (liftAnd z) (mz + 1) ∧ IsTree (liftAnd z) (tz + 1) ∧
      Gap (liftAnd z) 1 ∧ ForcedMulti (liftAnd z))
    ∧ (IsOpt (liftOr z) (mz + 1) ∧ IsTree (liftOr z) (tz + 1) ∧
      Gap (liftOr z) 1 ∧ ForcedMulti (liftOr z)) :=
  ⟨lift_lemma z mz tz hz0 hz1 hopt htree hgap hfm,
   lift_lemma_or z mz tz hz0 hz1 hopt htree hgap hfm⟩

#print axioms negF_negF
#print axioms circuitComputes_negF
#print axioms numReconv_negIn
#print axioms evalGates_negIn
#print axioms hasFormula_cnl
#print axioms liftOr_eq
#print axioms lift_lemma_or
#print axioms lift_lemma_both

theorem wireCost_eq_gate_wires (n : Nat) (m : Nat) (gs : List Gate)
    (hwf : wfC n gs) (hlen : gs.length = m) (hm : 0 < m)
    (hgw : ∀ p, p < m → p ≠ m - 1 → edgesToWire gs (n + p) = 1) :
    wireCost n gs (n + m) (n + (m - 1)) = m := by
  have hzero : edgesToWire gs (n + (m - 1)) = 0 := by
    have h := edges_last_eq_zero n gs hwf
    rw [hlen] at h; exact h
  have hmain := costList_aux n (n + m) gs.length gs (Nat.le_refl _) [n + (m - 1)] hwf
    (fun w hw => by rw [hlen] at hw; omega)
    (fun p hp => by
      rw [hlen] at hp
      simp only [List.count_singleton]
      by_cases he : p = m - 1
      · subst he
        have hb : ((n + (m - 1)) == n + (m - 1)) = true := by simp
        rw [hb, hzero]
        simp
      · have hb : ((n + (m - 1)) == n + p) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        rw [hb, hgw p hp he]
        simp)
    (fun r hr => by
      rcases List.mem_cons.mp hr with he | he2
      · subst he; rw [hlen]; omega
      · cases he2)
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hmain
  omega

theorem gate_sharing_free_is_tree (n : Nat) (f : Func n) (m : Nat) (gs : List Gate)
    (hwf : wfC n gs) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hgw : ∀ p, p < m → p ≠ m - 1 → edgesToWire gs (n + p) = 1) :
    HasFormula f m := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hgs
    rcases empty_only_const n f hc with hcf | hcf
    · exact ⟨.one, by simp [gatesF], Or.inr (funext fun x => by simp [evalF, hcf x])⟩
    · exact ⟨.one, by simp [gatesF], Or.inl (funext fun x => by simp [evalF, hcf x])⟩
  · refine ⟨wireFrm n gs (n + m) (n + (m - 1)), ?_, ?_⟩
    · rw [gatesF_wireFrm]
      exact Nat.le_of_eq (wireCost_eq_gate_wires n m gs hwf hlen hm hgw)
    · exact formulaComputes_wireFrm n f m gs hwf hlen hc hm

#print axioms wireCost_eq_gate_wires
#print axioms gate_sharing_free_is_tree

theorem tree_thm_as_stated_is_false :
    ¬ (∀ (k : Nat) (f : Func k) (m t : Nat), IsOpt f m → IsTree f t → m ≤ 3 → t = m) := by
  intro h
  exact absurd (h 1 litZ 1 0 litZ_opt litZ_tree (by omega)) (by decide)

theorem litZ_isLiteral : IsLiteral litZ := ⟨0, false, by funext x; simp [litZ]⟩

theorem wireVal_in (x : Assign n) (vals : Array Bool) (w : Nat) (h : w < n) :
    wireVal x vals w = x ⟨w, h⟩ := by unfold wireVal; rw [dif_pos h]

theorem wireVal_gate (x : Assign n) (vals : Array Bool) (j : Nat) :
    wireVal x vals (n + j) = vals.getD j false := by
  unfold wireVal; rw [dif_neg (by omega)]; simp

def pol (g : Gate) (w : Nat) : Bool := if g.ia = w then g.na else g.nb
def opol (g : Gate) (w : Nat) : Bool := if g.ia = w then g.nb else g.na
def oidx (g : Gate) (w : Nat) : Nat := if g.ia = w then g.ib else g.ia

theorem peel_val (x : Assign n) (vals : Array Bool) (g : Gate) (w : Nat)
    (h : edgesTo g w = 1) :
    ((xor g.na (wireVal x vals g.ia)) && (xor g.nb (wireVal x vals g.ib)))
      = ((xor (pol g w) (wireVal x vals w))
         && (xor (opol g w) (wireVal x vals (oidx g w)))) := by
  unfold pol opol oidx
  by_cases ha : g.ia = w
  · rw [if_pos ha, if_pos ha, if_pos ha, ha]
  · rw [if_neg ha, if_neg ha, if_neg ha]
    have hb : g.ib = w := by
      unfold edgesTo at h
      rw [if_neg (by simpa using ha)] at h
      by_cases hb : (g.ib == w) = true
      · simpa using hb
      · rw [if_neg hb] at h; omega
    rw [hb]; exact Bool.and_comm _ _

theorem oidx_ne (g : Gate) (w : Nat) (h : edgesTo g w = 1) : oidx g w ≠ w := by
  unfold oidx edgesTo at *
  by_cases ha : g.ia = w
  · rw [if_pos ha]
    rw [if_pos (by simpa using ha)] at h
    intro hb; rw [if_pos (by simpa using hb)] at h; omega
  · rw [if_neg ha]; exact ha

theorem oidx_lt (g : Gate) (w k : Nat) (hia : g.ia < k) (hib : g.ib < k) : oidx g w < k := by
  unfold oidx; split <;> assumption

theorem edgesTo_pos_iff (g : Gate) (w : Nat) (h : 1 ≤ edgesTo g w) : g.ia = w ∨ g.ib = w := by
  unfold edgesTo at h
  by_cases ha : (g.ia == w) = true
  · exact Or.inl (by simpa using ha)
  · rw [if_neg ha] at h
    by_cases hb : (g.ib == w) = true
    · exact Or.inr (by simpa using hb)
    · rw [if_neg hb] at h; omega

theorem c_reads_b (f : Func n) (a b c : Gate)
    (hwf : wfC n [a, b, c]) (hopt : IsOpt f 3) (hc : CircuitComputes [a, b, c] f)
    (hcc : edgesTo c n = 1) : oidx c n = n + 1 := by
  have hpos : 1 ≤ edgesToWire [a, b, c] (n + 1) :=
    edges_pos_of_nondead n f [a, b, c] 3 hwf hopt (by simp) hc 1 (by simp)
  have hwa := hwf ⟨0, by simp⟩
  have hwb := hwf ⟨1, by simp⟩
  simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] at hwa hwb
  have ha0 : edgesTo a (n + 1) = 0 := by
    unfold edgesTo; rw [if_neg (by simp; omega), if_neg (by simp; omega)]
  have hb0 : edgesTo b (n + 1) = 0 := by
    unfold edgesTo; rw [if_neg (by simp; omega), if_neg (by simp; omega)]
  have hsum : edgesToWire [a, b, c] (n + 1) = edgesTo a (n+1) + edgesTo b (n+1) + edgesTo c (n+1) := by
    unfold edgesToWire; simp [List.sum_cons]; omega
  have hc1 : 1 ≤ edgesTo c (n + 1) := by omega
  rcases edgesTo_pos_iff c (n + 1) hc1 with h | h
  ·
    unfold oidx
    rw [if_neg (by omega)]
    exact h
  ·
    unfold oidx
    by_cases hia : c.ia = n
    · rw [if_pos hia]; exact h
    · exfalso
      have : c.ib = n := by
        unfold edgesTo at hcc
        rw [if_neg (by simpa using hia)] at hcc
        by_cases hb : (c.ib == n) = true
        · simpa using hb
        · rw [if_neg hb] at hcc; omega
      omega

theorem v0_of (x : Assign n) (gs : List Gate) (hwf : wfC n gs) (h : 0 < gs.length)
    (h1 : (gs[0]).ia < n) (h2 : (gs[0]).ib < n) :
    (evalGates x gs).getD 0 false
      = ((xor (gs[0]).na (x ⟨(gs[0]).ia, h1⟩)) && (xor (gs[0]).nb (x ⟨(gs[0]).ib, h2⟩))) := by
  rw [getD_evalGates_eq n x gs 0 h hwf, wireVal_in x _ _ h1, wireVal_in x _ _ h2]

theorem out2 (x : Assign n) (a g : Gate) (hwf : wfC n [a, g]) :
    circuitOut x [a, g]
      = ((xor g.na (wireVal x (evalGates x [a,g]) g.ia))
         && (xor g.nb (wireVal x (evalGates x [a,g]) g.ib))) := by
  unfold circuitOut
  rw [show ([a,g] : List Gate).length - 1 = 1 from by simp]
  exact getD_evalGates_eq n x [a,g] 1 (by simp) hwf

theorem out3 (x : Assign n) (a b c : Gate) (hwf : wfC n [a, b, c]) :
    circuitOut x [a, b, c]
      = ((xor c.na (wireVal x (evalGates x [a,b,c]) c.ia))
         && (xor c.nb (wireVal x (evalGates x [a,b,c]) c.ib))) := by
  unfold circuitOut
  rw [show ([a,b,c] : List Gate).length - 1 = 2 from by simp]
  exact getD_evalGates_eq n x [a,b,c] 2 (by simp) hwf

theorem v1_of (x : Assign n) (a b c : Gate) (hwf : wfC n [a, b, c]) :
    (evalGates x [a, b, c]).getD 1 false
      = ((xor b.na (wireVal x (evalGates x [a,b,c]) b.ia))
         && (xor b.nb (wireVal x (evalGates x [a,b,c]) b.ib))) :=
  getD_evalGates_eq n x [a,b,c] 1 (by simp) hwf

theorem wireVal_gate0 (x : Assign n) (vals : Array Bool) :
    wireVal x vals n = vals.getD 0 false := by
  unfold wireVal; rw [dif_neg (by omega)]; simp

theorem key_out (x : Assign n) (a b c : Gate) (hwf : wfC n [a,b,c])
    (hb : edgesTo b n = 1) (hcc : edgesTo c n = 1) (hcb : oidx c n = n + 1)
    (hW : oidx b n < n) :
    circuitOut x [a,b,c]
      = ((xor (pol c n) ((evalGates x [a,b,c]).getD 0 false))
         && (xor (opol c n)
              ((xor (pol b n) ((evalGates x [a,b,c]).getD 0 false))
               && (xor (opol b n) (x ⟨oidx b n, hW⟩))))) := by
  rw [out3 x a b c hwf, peel_val x (evalGates x [a,b,c]) c n hcc, hcb,
      wireVal_gate0, wireVal_gate x (evalGates x [a,b,c]) 1,
      v1_of x a b c hwf, peel_val x (evalGates x [a,b,c]) b n hb,
      wireVal_gate0, wireVal_in x (evalGates x [a,b,c]) (oidx b n) hW]

theorem v0_3 (x : Assign n) (a b c : Gate) (hwf : wfC n [a,b,c]) (h1 : a.ia < n) (h2 : a.ib < n) :
    (evalGates x [a,b,c]).getD 0 false
      = ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))) := by
  rw [getD_evalGates_eq n x [a,b,c] 0 (by simp) hwf]
  simp only [List.getElem_cons_zero]
  rw [wireVal_in x _ a.ia h1, wireVal_in x _ a.ib h2]

theorem v0_2 (x : Assign n) (a g : Gate) (hwf : wfC n [a,g]) (h1 : a.ia < n) (h2 : a.ib < n) :
    (evalGates x [a,g]).getD 0 false
      = ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))) := by
  rw [getD_evalGates_eq n x [a,g] 0 (by simp) hwf]
  simp only [List.getElem_cons_zero]
  rw [wireVal_in x _ a.ia h1, wireVal_in x _ a.ib h2]

theorem v0_1 (x : Assign n) (a : Gate) (hwf : wfC n [a]) (h1 : a.ia < n) (h2 : a.ib < n) :
    circuitOut x [a] = ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))) := by
  unfold circuitOut
  rw [show ([a] : List Gate).length - 1 = 0 from by simp,
      getD_evalGates_eq n x [a] 0 (by simp) hwf]
  simp only [List.getElem_cons_zero]
  rw [wireVal_in x _ a.ia h1, wireVal_in x _ a.ib h2]

theorem hasCircuit2_of_agree (f : Func n) (gs2 gs3 : List Gate) (hwf2 : wfC n gs2)
    (hlen : gs2.length ≤ 2) (hc : CircuitComputes gs3 f)
    (heq : ∀ x : Assign n, circuitOut x gs2 = circuitOut x gs3) : HasCircuit f 2 := by
  refine ⟨gs2, hwf2, hlen, ?_⟩
  rcases hc with h | h
  · exact Or.inl (fun x => by rw [heq x, h x])
  · exact Or.inr (fun x => by rw [heq x, h x])

theorem wfC_two (a : Gate) (d beta : Bool) (W : Nat)
    (h1 : a.ia < n) (h2 : a.ib < n) (hW : W < n) :
    wfC n [a, (⟨d, n, beta, W⟩ : Gate)] := by
  intro p
  rcases p with ⟨pv, hpv⟩
  match pv, hpv with
  | 0, _ => exact ⟨by simpa using h1, by simpa using h2⟩
  | 1, _ => exact ⟨by simp, by simp; omega⟩
  | (k+2), h => exact absurd h (by simp)

theorem out2_lit (x : Assign n) (a : Gate) (d beta : Bool) (W : Nat)
    (h1 : a.ia < n) (h2 : a.ib < n) (hW : W < n) :
    circuitOut x [a, (⟨d, n, beta, W⟩ : Gate)]
      = ((xor d ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))))
         && (xor beta (x ⟨W, hW⟩))) := by
  have hw2 := wfC_two a d beta W h1 h2 hW
  rw [out2 x a ⟨d, n, beta, W⟩ hw2]
  show ((xor d (wireVal x (evalGates x [a, (⟨d, n, beta, W⟩ : Gate)]) n))
        && (xor beta (wireVal x (evalGates x [a, (⟨d, n, beta, W⟩ : Gate)]) W))) = _
  rw [wireVal_gate0, wireVal_in x _ W hW, v0_2 x a ⟨d, n, beta, W⟩ hw2 h1 h2]

theorem wfC_two_nn (a : Gate) (d : Bool) (h1 : a.ia < n) (h2 : a.ib < n) :
    wfC n [a, (⟨d, n, d, n⟩ : Gate)] := by
  intro p
  rcases p with ⟨pv, hpv⟩
  match pv, hpv with
  | 0, _ => exact ⟨by simpa using h1, by simpa using h2⟩
  | 1, _ => exact ⟨by simp, by simp⟩
  | (k+2), h => exact absurd h (by simp)

theorem out2_lit_nn (x : Assign n) (a : Gate) (d : Bool)
    (h1 : a.ia < n) (h2 : a.ib < n) :
    circuitOut x [a, (⟨d, n, d, n⟩ : Gate)]
      = (xor d ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩)))) := by
  have hw2 := wfC_two_nn a d h1 h2
  rw [out2 x a ⟨d, n, d, n⟩ hw2]
  show ((xor d (wireVal x (evalGates x [a, (⟨d, n, d, n⟩ : Gate)]) n))
        && (xor d (wireVal x (evalGates x [a, (⟨d, n, d, n⟩ : Gate)]) n))) = _
  rw [wireVal_gate0, v0_2 x a ⟨d, n, d, n⟩ hw2 h1 h2, Bool.and_self]

theorem wfC_one (a : Gate) (h1 : a.ia < n) (h2 : a.ib < n) : wfC n [a] := by
  intro p
  rcases p with ⟨pv, hpv⟩
  match pv, hpv with
  | 0, _ => exact ⟨by simpa using h1, by simpa using h2⟩
  | (k+1), h => exact absurd h (by simp)

theorem ne_const_of_opt_pos (f : Func n) (m : Nat) (hopt : IsOpt f m) (hm : 0 < m) :
    f ≠ (fun _ => false) ∧ f ≠ (fun _ => true) := by
  constructor
  · intro h
    have : HasCircuit f 0 := ⟨[], (fun i => absurd i.isLt (by simp)), Nat.le_refl _,
      Or.inl (fun x => by rw [h]; rfl)⟩
    exact absurd (hopt.2 0 this) (by omega)
  · intro h
    have : HasCircuit f 0 := ⟨[], (fun i => absurd i.isLt (by simp)), Nat.le_refl _,
      Or.inr (fun x => by rw [h]; rfl)⟩
    exact absurd (hopt.2 0 this) (by omega)

theorem absorb1 (d al P A : Bool) :
    ((xor d P) && (xor false ((xor d P) && (xor al A)))) = ((xor d P) && (xor al A)) := by
  cases d <;> cases al <;> cases P <;> cases A <;> rfl
theorem absorb2 (d al P A : Bool) :
    ((xor d P) && (xor false ((xor (!d) P) && (xor al A)))) = false := by
  cases d <;> cases al <;> cases P <;> cases A <;> rfl
theorem absorb3 (d al P A : Bool) :
    ((xor d P) && (xor true ((xor d P) && (xor al A)))) = ((xor d P) && (xor (!al) A)) := by
  cases d <;> cases al <;> cases P <;> cases A <;> rfl
theorem absorb4 (d al P A : Bool) :
    ((xor d P) && (xor true ((xor (!d) P) && (xor al A)))) = (xor d P) := by
  cases d <;> cases al <;> cases P <;> cases A <;> rfl

theorem absorb_three (f : Func n) (a b c : Gate)
    (hwf : wfC n [a, b, c]) (hopt : IsOpt f 3) (hc : CircuitComputes [a, b, c] f)
    (hb : edgesTo b n = 1) (hcc : edgesTo c n = 1) : False := by
  have hwa := hwf ⟨0, by simp⟩
  have hwb := hwf ⟨1, by simp⟩
  simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] at hwa hwb
  have h1 : a.ia < n := by omega
  have h2 : a.ib < n := by omega
  have hcb := c_reads_b f a b c hwf hopt hc hcc
  have hW : oidx b n < n := by
    have hx := oidx_lt b n (n + 1) hwb.1 hwb.2
    have hy := oidx_ne b n hb
    omega
  have hout : ∀ x : Assign n, circuitOut x [a, b, c]
      = ((xor (pol c n) ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))))
         && (xor (opol c n)
              ((xor (pol b n) ((xor a.na (x ⟨a.ia, h1⟩)) && (xor a.nb (x ⟨a.ib, h2⟩))))
               && (xor (opol b n) (x ⟨oidx b n, hW⟩))))) := fun x => by
    rw [key_out x a b c hwf hb hcc hcb hW, v0_3 x a b c hwf h1 h2]
  have h32 : ¬ (3 ≤ 2) := by omega
  by_cases hde : pol c n = pol b n
  · cases hgc : opol c n with
    | false =>
        refine h32 (hopt.2 2 (hasCircuit2_of_agree f
          [a, (⟨pol c n, n, opol b n, oidx b n⟩ : Gate)] [a, b, c]
          (wfC_two a (pol c n) (opol b n) (oidx b n) h1 h2 hW) (by simp) hc (fun x => ?_)))
        rw [out2_lit x a (pol c n) (opol b n) (oidx b n) h1 h2 hW, hout x, hgc, ← hde]
        exact (absorb1 _ _ _ _).symm
    | true =>
        refine h32 (hopt.2 2 (hasCircuit2_of_agree f
          [a, (⟨pol c n, n, !(opol b n), oidx b n⟩ : Gate)] [a, b, c]
          (wfC_two a (pol c n) (!(opol b n)) (oidx b n) h1 h2 hW) (by simp) hc (fun x => ?_)))
        rw [out2_lit x a (pol c n) (!(opol b n)) (oidx b n) h1 h2 hW, hout x, hgc, ← hde]
        exact (absorb3 _ _ _ _).symm
  · have hpb : pol b n = !(pol c n) := by
      cases hx : pol c n <;> cases hy : pol b n <;> simp_all
    cases hgc : opol c n with
    | false =>
        obtain ⟨hn0, hn1⟩ := ne_const_of_opt_pos f 3 hopt (by omega)
        have hfalse : ∀ x : Assign n, circuitOut x [a, b, c] = false := fun x => by
          rw [hout x, hgc, hpb]; exact absorb2 _ _ _ _
        rcases hc with h | h
        · exact hn0 (funext fun x => by rw [← h x, hfalse x])
        · exact hn1 (funext fun x => by
            have e := h x
            rw [hfalse x] at e
            cases hv : f x with
            | false => rw [hv] at e; simp at e
            | true => rfl)
    | true =>
        refine h32 (hopt.2 2 (hasCircuit2_of_agree f
          [a, (⟨pol c n, n, pol c n, n⟩ : Gate)] [a, b, c]
          (wfC_two_nn a (pol c n) h1 h2) (by simp) hc (fun x => ?_)))
        rw [out2_lit_nn x a (pol c n) h1 h2, hout x, hgc, hpb]
        exact (absorb4 _ _ _ _).symm

theorem edgesTo_le_two (g : Gate) (w : Nat) : edgesTo g w ≤ 2 := by
  unfold edgesTo
  split <;> split <;> omega

theorem edgesTo_eq_zero (g : Gate) (w : Nat) (ha : g.ia ≠ w) (hb : g.ib ≠ w) :
    edgesTo g w = 0 := by
  unfold edgesTo
  rw [if_neg (by simpa using ha), if_neg (by simpa using hb)]

theorem dup_of_two (g : Gate) (w : Nat) (h : 2 ≤ edgesTo g w) : g.ia = w ∧ g.ib = w := by
  unfold edgesTo at h
  constructor
  · by_cases hh : (g.ia == w) = true
    · simpa using hh
    · rw [if_neg hh] at h; exfalso; revert h; split <;> omega
  · by_cases hh : (g.ib == w) = true
    · simpa using hh
    · rw [if_neg hh] at h; exfalso; revert h; split <;> omega

theorem edgesToWire3 (a b c : Gate) (w : Nat) :
    edgesToWire [a, b, c] w = edgesTo a w + edgesTo b w + edgesTo c w := by
  unfold edgesToWire
  simp [List.sum_cons]
  omega

theorem edgesToWire2 (a b : Gate) (w : Nat) :
    edgesToWire [a, b] w = edgesTo a w + edgesTo b w := by
  unfold edgesToWire
  simp [List.sum_cons]

theorem edgesTo_le_one_gate (f : Func n) (m : Nat) (gs : List Gate)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hm : 0 < m) (j : Nat) (hj : j < gs.length) (w : Nat) (hnw : n ≤ w) :
    edgesTo (gs[j]) w ≤ 1 := by
  rcases Nat.lt_or_ge (edgesTo (gs[j]) w) 2 with h | h
  · omega
  · exfalso
    obtain ⟨ha, hb⟩ := dup_of_two (gs[j]) w h
    obtain ⟨h0, h1⟩ := ne_const_of_opt_pos f m hopt hm
    exact opt_no_dup_gate_wire_full n f gs m h0 h1 hwf hopt hlen hc j hj
      (by rw [ha]; exact hnw) (by rw [ha, hb])

theorem edgesTo_earlier_zero (gs : List Gate) (hwf : wfC n gs) (j p : Nat)
    (hj : j < gs.length) (hjp : j ≤ p) : edgesTo (gs[j]) (n + p) = 0 := by
  have h := hwf ⟨j, hj⟩
  simp only [List.get_eq_getElem] at h
  exact edgesTo_eq_zero _ _ (by omega) (by omega)

theorem edgesToWire_le_one (f : Func n) (m : Nat) (gs : List Gate)
    (hwf : wfC n gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hle : m ≤ 3) (p : Nat) (hp : p < m) (hne : p ≠ m - 1) :
    edgesToWire gs (n + p) ≤ 1 := by
  have hm : 0 < m := by omega
  match gs, hlen with
  | [], h =>
      exfalso
      have : m = 0 := by simpa using h.symm
      omega
  | [a], h =>
      exfalso
      have hm1 : m = 1 := by simpa using h.symm
      omega
  | [a, b], h =>
      have hm2 : m = 2 := by simpa using h.symm
      have hp0 : p = 0 := by omega
      subst hp0
      rw [edgesToWire2]
      have h0 : edgesTo a (n + 0) = 0 :=
        edgesTo_earlier_zero [a, b] hwf 0 0 (by simp) (Nat.le_refl _)
      have h1 : edgesTo b (n + 0) ≤ 1 :=
        edgesTo_le_one_gate f m [a, b] hwf hopt h hc hm 1 (by simp) (n + 0) (by omega)
      omega
  | [a, b, c], h =>
      have hm3 : m = 3 := by simpa using h.symm
      rw [edgesToWire3]
      have h0 : edgesTo a (n + p) = 0 :=
        edgesTo_earlier_zero [a, b, c] hwf 0 p (by simp) (by omega)
      have h2 : edgesTo c (n + p) ≤ 1 :=
        edgesTo_le_one_gate f m [a, b, c] hwf hopt h hc hm 2 (by simp) (n + p) (by omega)
      rcases Nat.lt_or_ge p 1 with hp0 | hp1
      · have hp0' : p = 0 := by omega
        subst hp0'
        have h1 : edgesTo b (n + 0) ≤ 1 :=
          edgesTo_le_one_gate f m [a, b, c] hwf hopt h hc hm 1 (by simp) (n + 0) (by omega)
        rcases Nat.lt_or_ge (edgesTo b (n + 0) + edgesTo c (n + 0)) 2 with hlt | hge
        · omega
        · exfalso
          have hopt3 : IsOpt f 3 := by rw [← hm3]; exact hopt
          exact absorb_three f a b c hwf hopt3 hc (by simpa using (by omega : edgesTo b (n+0) = 1))
            (by simpa using (by omega : edgesTo c (n+0) = 1))
      · have hp1' : p = 1 := by omega
        subst hp1'
        have h1 : edgesTo b (n + 1) = 0 :=
          edgesTo_earlier_zero [a, b, c] hwf 1 1 (by simp) (Nat.le_refl _)
        omega
  | (a :: b :: c :: d :: rest), h =>
      exfalso
      have : m = rest.length + 1 + 1 + 1 + 1 := by simpa using h.symm
      omega

theorem tree_le_opt_of_le_three (f : Func n) (m t : Nat)
    (hopt : IsOpt f m) (htree : IsTree f t) (hle : m ≤ 3) :
    t ≤ m := by
  obtain ⟨gs, hwf, hlen0, hc⟩ := hopt.1
  have hlen : gs.length = m :=
    Nat.le_antisymm hlen0 (hopt.2 _ ⟨gs, hwf, Nat.le_refl _, hc⟩)
  refine htree.2 m (gate_sharing_free_is_tree n f m gs hwf hlen hc (fun p hp hne => ?_))
  have hm : 0 < m := by omega
  have hpos : 1 ≤ edgesToWire gs (n + p) :=
    edges_pos_of_nondead n f gs m hwf hopt hlen hc p (by rw [hlen]; omega)
  have hup := edgesToWire_le_one f m gs hwf hopt hlen hc hle p hp hne
  omega

def shiftW (n d w : Nat) : Nat := if w < n then w else w + d
def shiftG (n d : Nat) (g : Gate) : Gate :=
  ⟨g.na, shiftW n d g.ia, g.nb, shiftW n d g.ib⟩
def shiftC (n d : Nat) (gs : List Gate) : List Gate := gs.map (shiftG n d)

theorem length_shiftC (n d : Nat) (gs : List Gate) : (shiftC n d gs).length = gs.length := by
  unfold shiftC; simp

theorem getElem_shiftC (n d : Nat) (gs : List Gate) (j : Nat) (hj : j < gs.length) :
    (shiftC n d gs)[j]' (by rw [length_shiftC]; exact hj) = shiftG n d gs[j] := by
  unfold shiftC; simp

theorem wfC_append_shift (ga gb : List Gate) (hwa : wfC n ga) (hwb : wfC n gb) :
    wfC n (ga ++ shiftC n ga.length gb) := by
  intro p
  rcases p with ⟨pv, hpv⟩
  simp only [List.get_eq_getElem]
  rw [List.length_append, length_shiftC] at hpv
  by_cases hlt : pv < ga.length
  · rw [List.getElem_append_left hlt]
    have h := hwa ⟨pv, hlt⟩
    simp only [List.get_eq_getElem] at h
    exact ⟨by omega, by omega⟩
  · have hge : ga.length ≤ pv := by omega
    have hj : pv - ga.length < (shiftC n ga.length gb).length := by
      rw [length_shiftC]; omega
    rw [List.getElem_append_right hge]
    rw [getElem_shiftC n ga.length gb (pv - ga.length) (by omega)]
    have h := hwb ⟨pv - ga.length, by omega⟩
    simp only [List.get_eq_getElem] at h
    refine ⟨?_, ?_⟩
    · unfold shiftG shiftW
      simp only []
      split <;> omega
    · unfold shiftG shiftW
      simp only []
      split <;> omega

theorem shift_step (x : Assign n) (ga gb : List Gate) (hwb : wfC n gb)
    (hwc : wfC n (ga ++ shiftC n ga.length gb)) (j : Nat) (hj : j < gb.length)
    (ih : ∀ i, i < j → i < gb.length →
      (evalGates x (ga ++ shiftC n ga.length gb)).getD (ga.length + i) false
        = (evalGates x gb).getD i false) :
    (evalGates x (ga ++ shiftC n ga.length gb)).getD (ga.length + j) false
      = (evalGates x gb).getD j false := by
  have hjc : ga.length + j < (ga ++ shiftC n ga.length gb).length := by
    rw [List.length_append, length_shiftC]; omega
  have hel : (ga ++ shiftC n ga.length gb)[ga.length + j] = shiftG n ga.length gb[j] := by
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact getElem_shiftC n ga.length gb j hj
  have hb := hwb ⟨j, hj⟩
  simp only [List.get_eq_getElem] at hb
  have key : ∀ w, w < n + j →
      wireVal x (evalGates x (ga ++ shiftC n ga.length gb)) (shiftW n ga.length w)
        = wireVal x (evalGates x gb) w := by
    intro w hw
    by_cases hlt : w < n
    · unfold shiftW
      rw [if_pos hlt, wireVal_in _ _ _ hlt, wireVal_in _ _ _ hlt]
    · unfold shiftW
      rw [if_neg hlt]
      obtain ⟨i, hi⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
      subst hi
      rw [show n + i + ga.length = n + (ga.length + i) from by omega,
          wireVal_gate, wireVal_gate]
      exact ih i (by omega) (by omega)
  rw [getD_evalGates_eq n x _ (ga.length + j) hjc hwc,
      getD_evalGates_eq n x gb j hj hwb, hel]
  unfold shiftG
  simp only []
  rw [key gb[j].ia (by omega), key gb[j].ib (by omega)]

theorem evalGates_shift_aux (x : Assign n) (ga gb : List Gate) (hwa : wfC n ga) (hwb : wfC n gb) :
    ∀ L j, j ≤ L → j < gb.length →
      (evalGates x (ga ++ shiftC n ga.length gb)).getD (ga.length + j) false
        = (evalGates x gb).getD j false := by
  have hwc := wfC_append_shift ga gb hwa hwb
  intro L
  induction L with
  | zero =>
      intro j hjL hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact shift_step x ga gb hwb hwc 0 hj (fun i hi _ => absurd hi (by omega))
  | succ L ih =>
      intro j hjL hj
      rcases Nat.lt_or_ge j (L + 1) with hlt | hge
      · exact ih j (by omega) hj
      · have hje : j = L + 1 := by omega
        subst hje
        exact shift_step x ga gb hwb hwc (L + 1) hj (fun i hi hib => ih i (by omega) hib)

theorem evalGates_shift (x : Assign n) (ga gb : List Gate) (hwa : wfC n ga) (hwb : wfC n gb)
    (j : Nat) (hj : j < gb.length) :
    (evalGates x (ga ++ shiftC n ga.length gb)).getD (ga.length + j) false
      = (evalGates x gb).getD j false :=
  evalGates_shift_aux x ga gb hwa hwb j j (Nat.le_refl _) hj

theorem evalGates_prefix (x : Assign n) (ga gb : List Gate) (j : Nat) (hj : j < ga.length) :
    (evalGates x (ga ++ shiftC n ga.length gb)).getD j false
      = (evalGates x ga).getD j false := by
  rw [getD_evalGates_take n x (ga ++ shiftC n ga.length gb) j
        (by rw [List.length_append, length_shiftC]; omega),
      getD_evalGates_take n x ga j hj]
  congr 2
  rw [List.take_append_of_le_length (by omega)]

inductive CR (n : Nat) where
  | cst : Bool → CR n
  | cir : List Gate → Nat → Bool → CR n

def flipCR : Bool → CR n → CR n
  | false, r => r
  | true, .cst b => .cst (!b)
  | true, .cir gs w fl => .cir gs w (!fl)

def combCR (pa : Bool) (ra : CR n) (pb : Bool) (rb : CR n) : CR n :=
  match ra, rb with
  | .cst ca, rb => if xor pa ca then flipCR pb rb else .cst false
  | ra, .cst cb => if xor pb cb then flipCR pa ra else .cst false
  | .cir ga wa fa, .cir gb wb fb =>
      .cir (ga ++ shiftC n ga.length gb
             ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n ga.length wb⟩ : Gate)])
           (n + (ga.length + gb.length)) false

def cmp : Frm n → CR n
  | .var i => .cir [] i.val false
  | .one => .cst true
  | .and pa a pb b => combCR pa (cmp a) pb (cmp b)

theorem getD_append_left (x : Assign n) (l r : List Gate) (j : Nat) (hj : j < l.length) :
    (evalGates x (l ++ r)).getD j false = (evalGates x l).getD j false := by
  rw [getD_evalGates_take n x (l ++ r) j (by simp; omega), getD_evalGates_take n x l j hj]
  congr 2
  rw [List.take_append_of_le_length (by omega)]

theorem wireVal_append_left (x : Assign n) (l r : List Gate) (w : Nat) (hw : w < n + l.length) :
    wireVal x (evalGates x (l ++ r)) w = wireVal x (evalGates x l) w := by
  by_cases hlt : w < n
  · rw [wireVal_in _ _ _ hlt, wireVal_in _ _ _ hlt]
  · obtain ⟨i, hi⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
    subst hi
    rw [wireVal_gate, wireVal_gate]
    exact getD_append_left x l r i (by omega)

def OkCR (g : Func n) (k : Nat) : CR n → Prop
  | .cst c => ∀ x : Assign n, g x = c
  | .cir gs w fl =>
      wfC n gs
      ∧ gs.length ≤ k
      ∧ ((gs = [] ∧ w < n) ∨ (gs ≠ [] ∧ w = n + (gs.length - 1)))
      ∧ (∀ x : Assign n, wireVal x (evalGates x gs) w = xor fl (g x))

theorem ok_mono (g : Func n) (k k' : Nat) (hk : k ≤ k') (r : CR n) (h : OkCR g k r) :
    OkCR g k' r := by
  cases r with
  | cst c => exact h
  | cir gs w fl => exact ⟨h.1, Nat.le_trans h.2.1 hk, h.2.2.1, h.2.2.2⟩

theorem ok_flip (g : Func n) (k : Nat) (p : Bool) (r : CR n) (h : OkCR g k r) :
    OkCR (fun x => xor p (g x)) k (flipCR p r) := by
  cases p with
  | false =>
      cases r with
      | cst c => intro x; simpa using h x
      | cir gs w fl => exact ⟨h.1, h.2.1, h.2.2.1, fun x => by simpa using h.2.2.2 x⟩
  | true =>
      cases r with
      | cst c => intro x; simp [h x]
      | cir gs w fl =>
          refine ⟨h.1, h.2.1, h.2.2.1, fun x => ?_⟩
          rw [h.2.2.2 x]
          cases fl <;> cases hg : g x <;> simp [hg]

theorem len_pos (l : List Gate) (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

theorem ok_congr (g g' : Func n) (k : Nat) (r : CR n) (h : OkCR g k r) (he : ∀ x, g x = g' x) :
    OkCR g' k r := by
  cases r with
  | cst c => intro x; rw [← he x]; exact h x
  | cir gs w fl =>
      refine ⟨h.1, h.2.1, h.2.2.1, fun x => ?_⟩
      rw [h.2.2.2 x, he x]

theorem wfC_snoc (l : List Gate) (g : Gate) (hl : wfC n l)
    (h1 : g.ia < n + l.length) (h2 : g.ib < n + l.length) : wfC n (l ++ [g]) := by
  intro p
  rcases p with ⟨pv, hpv⟩
  simp only [List.get_eq_getElem]
  rw [List.length_append, List.length_singleton] at hpv
  by_cases hlt : pv < l.length
  · rw [List.getElem_append_left hlt]
    have h := hl ⟨pv, hlt⟩
    simp only [List.get_eq_getElem] at h
    exact ⟨by omega, by omega⟩
  · have hpe : pv = l.length := by omega
    subst hpe
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem_cons_zero]
    exact ⟨by omega, by omega⟩

theorem wireVal_shifted (x : Assign n) (ga gb : List Gate) (hwa : wfC n ga) (hwb : wfC n gb)
    (w : Nat) (hw : w < n + gb.length) :
    wireVal x (evalGates x (ga ++ shiftC n ga.length gb)) (shiftW n ga.length w)
      = wireVal x (evalGates x gb) w := by
  by_cases hlt : w < n
  · unfold shiftW
    rw [if_pos hlt, wireVal_in _ _ _ hlt, wireVal_in _ _ _ hlt]
  · unfold shiftW
    rw [if_neg hlt]
    obtain ⟨i, hi⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
    subst hi
    rw [show n + i + ga.length = n + (ga.length + i) from by omega,
        wireVal_gate, wireVal_gate]
    exact evalGates_shift x ga gb hwa hwb i (by omega)

theorem combCR_ok (pa pb : Bool) (ga gb : Func n) (ka kb : Nat) (ra rb : CR n)
    (ha : OkCR ga ka ra) (hb : OkCR gb kb rb) :
    OkCR (fun x => (xor pa (ga x)) && (xor pb (gb x))) (1 + ka + kb) (combCR pa ra pb rb) := by
  cases ra with
  | cst ca =>
      show OkCR _ _ (if xor pa ca then flipCR pb rb else .cst false)
      by_cases hc : xor pa ca = true
      · rw [if_pos hc]
        refine ok_congr (fun x => xor pb (gb x)) _ _ _
          (ok_mono _ kb (1 + ka + kb) (by omega) _ (ok_flip gb kb pb rb hb)) (fun x => ?_)
        rw [ha x, hc]
        simp
      · have hcf : xor pa ca = false := by simpa using hc
        rw [if_neg hc]
        intro x
        show ((xor pa (ga x)) && (xor pb (gb x))) = false
        rw [ha x, hcf]
        rfl
  | cir gsa wa fa =>
      cases rb with
      | cst cb =>
          show OkCR _ _ (if xor pb cb then flipCR pa (CR.cir gsa wa fa) else .cst false)
          by_cases hc : xor pb cb = true
          · rw [if_pos hc]
            refine ok_congr (fun x => xor pa (ga x)) _ _ _
              (ok_mono _ ka (1 + ka + kb) (by omega) _ (ok_flip ga ka pa _ ha)) (fun x => ?_)
            rw [hb x, hc]
            simp
          · have hcf : xor pb cb = false := by simpa using hc
            rw [if_neg hc]
            intro x
            show ((xor pa (ga x)) && (xor pb (gb x))) = false
            rw [hb x, hcf]
            simp
      | cir gsb wb fb =>
          have hwa : wfC n gsa := ha.1
          have hwb : wfC n gsb := hb.1
          have hva : wa < n + gsa.length := by
            rcases ha.2.2.1 with ⟨he, hlt⟩ | ⟨hne, heq⟩
            · have h0 : gsa.length = 0 := by rw [he]; rfl
              omega
            · have := len_pos gsa hne; omega
          have hvb : wb < n + gsb.length := by
            rcases hb.2.2.1 with ⟨he, hlt⟩ | ⟨hne, heq⟩
            · have h0 : gsb.length = 0 := by rw [he]; rfl
              omega
            · have := len_pos gsb hne; omega
          have hwl : wfC n (gsa ++ shiftC n gsa.length gsb) := wfC_append_shift gsa gsb hwa hwb
          have hll : (gsa ++ shiftC n gsa.length gsb).length = gsa.length + gsb.length := by
            rw [List.length_append, length_shiftC]
          have hsw : shiftW n gsa.length wb < n + (gsa.length + gsb.length) := by
            unfold shiftW; split <;> omega
          have hwf : wfC n (gsa ++ shiftC n gsa.length gsb
              ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)]) :=
            wfC_snoc _ _ hwl
              (by show wa < n + (gsa ++ shiftC n gsa.length gsb).length; rw [hll]; omega)
              (by show shiftW n gsa.length wb < n + (gsa ++ shiftC n gsa.length gsb).length
                  rw [hll]; exact hsw)
          have hlen : (gsa ++ shiftC n gsa.length gsb
              ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)]).length
              = gsa.length + gsb.length + 1 := by
            rw [List.length_append, hll, List.length_singleton]
          refine ⟨hwf, ?_, Or.inr ⟨by simp, by rw [hlen]; omega⟩, fun x => ?_⟩
          · rw [hlen]
            have h1 := ha.2.1; have h2 := hb.2.1; omega
          · have hidx : gsa.length + gsb.length < (gsa ++ shiftC n gsa.length gsb
                ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)]).length := by
              rw [hlen]; omega
            have hel : (gsa ++ shiftC n gsa.length gsb
                ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)])[
                  gsa.length + gsb.length]
                = (⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate) := by
              rw [List.getElem_append_right (by rw [hll]; omega)]
              simp [hll]
            rw [wireVal_gate, getD_evalGates_eq n x _ (gsa.length + gsb.length) hidx hwf, hel]
            have e1 : wireVal x (evalGates x (gsa ++ shiftC n gsa.length gsb
                  ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)])) wa
                = xor fa (ga x) := by
              rw [wireVal_append_left x (gsa ++ shiftC n gsa.length gsb) _ wa (by rw [hll]; omega),
                  wireVal_append_left x gsa _ wa hva]
              exact ha.2.2.2 x
            have e2 : wireVal x (evalGates x (gsa ++ shiftC n gsa.length gsb
                  ++ [(⟨xor pa fa, wa, xor pb fb, shiftW n gsa.length wb⟩ : Gate)]))
                  (shiftW n gsa.length wb)
                = xor fb (gb x) := by
              rw [wireVal_append_left x (gsa ++ shiftC n gsa.length gsb) _ _ (by rw [hll]; exact hsw),
                  wireVal_shifted x gsa gsb hwa hwb wb hvb]
              exact hb.2.2.2 x
            simp only []
            rw [e1, e2]
            cases pa <;> cases pb <;> cases fa <;> cases fb <;> cases ga x <;>
              cases gb x <;> simp

theorem cmp_ok : ∀ φ : Frm n, OkCR (evalF φ) (gatesF φ) (cmp φ) := by
  intro φ
  induction φ with
  | var i =>
      refine ⟨(fun p => absurd p.isLt (by simp)), by simp [gatesF], Or.inl ⟨rfl, i.isLt⟩, ?_⟩
      intro x
      rw [wireVal_in x _ i.val i.isLt]
      show x ⟨i.val, i.isLt⟩ = xor false (x i)
      simp
  | one => intro x; rfl
  | and pa a pb b iha ihb =>
      have h := combCR_ok pa pb (evalF a) (evalF b) (gatesF a) (gatesF b) _ _ iha ihb
      exact h

theorem opt_le_tree_of_not_literal (f : Func n) (m t : Nat)
    (hopt : IsOpt f m) (htree : IsTree f t) (hnl : ¬ IsLiteral f) : m ≤ t := by
  obtain ⟨φ, hg, hfc⟩ := htree.1
  have hok := cmp_ok φ
  cases hcr : cmp φ with
  | cst c =>

      rw [hcr] at hok
      obtain ⟨d, hd⟩ : ∃ d : Bool, ∀ x : Assign n, f x = d := by
        rcases hfc with h | h
        · exact ⟨c, fun x => by rw [← h]; exact hok x⟩
        · refine ⟨!c, fun x => ?_⟩
          have e : (!(f x)) = c := by rw [← congrFun h x]; exact hok x
          cases hf : f x <;> cases hc2 : c <;> simp_all
      have h0 : HasCircuit f 0 := by
        refine ⟨[], (fun p => absurd p.isLt (by simp)), Nat.le_refl _, ?_⟩
        cases d with
        | false => exact Or.inl (fun x => by rw [hd x]; rfl)
        | true => exact Or.inr (fun x => by rw [hd x]; rfl)
      exact Nat.le_trans (hopt.2 0 h0) (Nat.zero_le t)
  | cir gs w fl =>
      rw [hcr] at hok
      obtain ⟨hwf, hsz, hshape, hsem⟩ := hok
      rcases hshape with ⟨hnil, hlt⟩ | ⟨hne, heq⟩
      ·
        exfalso
        subst hnil
        have hlit : ∀ x : Assign n, evalF φ x = xor fl (x ⟨w, hlt⟩) := by
          intro x
          have := hsem x
          rw [wireVal_in x _ w hlt] at this
          cases hv : fl <;> cases hw : (x ⟨w, hlt⟩) <;> simp_all
        refine hnl ?_
        rcases hfc with h | h
        · exact ⟨⟨w, hlt⟩, fl, funext fun x => by rw [← h]; exact hlit x⟩
        · refine ⟨⟨w, hlt⟩, !fl, funext fun x => ?_⟩
          have e := hlit x
          rw [h] at e
          cases hv : fl <;> cases hf : f x <;> simp_all
      ·
        have hout : ∀ x : Assign n, circuitOut x gs = xor fl (evalF φ x) := by
          intro x
          have := hsem x
          rw [heq, wireVal_gate] at this
          exact this
        refine hopt.2 t ⟨gs, hwf, Nat.le_trans hsz hg, ?_⟩
        rcases hfc with h | h
        · cases fl with
          | false => exact Or.inl (fun x => by rw [hout x, h]; simp)
          | true => exact Or.inr (fun x => by rw [hout x, h]; simp)
        · cases fl with
          | false => exact Or.inr (fun x => by rw [hout x, h]; simp)
          | true =>
              refine Or.inl (fun x => ?_)
              rw [hout x, h]
              cases hf : f x <;> simp [hf]

theorem tree_thm (f : Func n) (m t : Nat)
    (hopt : IsOpt f m) (htree : IsTree f t)
    (hle : m ≤ 3) (hnl : ¬ IsLiteral f) :
    t = m :=
  Nat.le_antisymm (tree_le_opt_of_le_three f m t hopt htree hle)
    (opt_le_tree_of_not_literal f m t hopt htree hnl)

#print axioms tree_thm_as_stated_is_false
#print axioms absorb_three
#print axioms edgesToWire_le_one
#print axioms tree_le_opt_of_le_three
#print axioms opt_le_tree_of_not_literal
#print axioms tree_thm

end ThresholdTree
