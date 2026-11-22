import ThresholdTree
set_option maxRecDepth 100000
namespace Witness4
open ThresholdTree

def asg (t : Nat) : Assign 4 := fun i => (t >>> i.val) % 2 == 1

def idx (x : Assign 4) : Nat :=
  (if x 0 then 1 else 0) + 2 * (if x 1 then 1 else 0)
    + 4 * (if x 2 then 1 else 0) + 8 * (if x 3 then 1 else 0)

theorem asg_idx (x : Assign 4) : asg (idx x) = x := by
  funext i
  have h4 : i.val < 4 := i.isLt
  match i, h4 with
  | ⟨0, _⟩, _ => cases hx : x 0 <;> simp [asg, idx, hx] <;>
      (cases x 1 <;> cases x 2 <;> cases x 3 <;> simp)
  | ⟨1, _⟩, _ => cases hx : x 1 <;> simp [asg, idx, hx] <;>
      (cases x 0 <;> cases x 2 <;> cases x 3 <;> simp)
  | ⟨2, _⟩, _ => cases hx : x 2 <;> simp [asg, idx, hx] <;>
      (cases x 0 <;> cases x 1 <;> cases x 3 <;> simp)
  | ⟨3, _⟩, _ => cases hx : x 3 <;> simp [asg, idx, hx] <;>
      (cases x 0 <;> cases x 1 <;> cases x 2 <;> simp)

theorem idx_lt (x : Assign 4) : idx x < 16 := by
  simp only [idx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> simp

theorem funext16 {f g : Func 4} (h : ∀ t, t < 16 → f (asg t) = g (asg t)) : f = g := by
  funext x
  have hx := h (idx x) (idx_lt x)
  rw [asg_idx] at hx
  exact hx

theorem funext16' {f g : Func 4}
    (h : (List.range 16).all (fun t => f (asg t) == g (asg t)) = true) : f = g := by
  refine funext16 (fun t ht => ?_)
  have hm : t ∈ List.range 16 := List.mem_range.mpr ht
  exact of_decide_eq_true ((List.all_eq_true.mp h) t hm)

def tab (f : Func 4) : List Bool := (List.range 16).map (fun t => f (asg t))
def tand (pa : Bool) (a : List Bool) (pb : Bool) (b : List Bool) : List Bool :=
  List.zipWith (fun u v => (xor pa u) && (xor pb v)) a b
def key : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * key l
def unkey : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, j => (j % 2 == 1) :: unkey n (j / 2)

abbrev Marks := Array Bool
def emptyM : Marks := Array.replicate 65536 false
@[inline] def has (t : Marks) (j : Nat) : Bool := (t[j]?).getD false
def add (t : Marks) (v : List Bool) : Marks := t.set! (key v) true

theorem size_add (t : Marks) (v : List Bool) : (add t v).size = t.size := by
  simp [add, Array.set!]

theorem has_add_mono {t : Marks} {v : List Bool} {j : Nat} (h : has t j = true) :
    has (add t v) j = true := by
  unfold has add
  rw [Array.set!, Array.getElem?_setIfInBounds]
  by_cases hij : key v = j
  · rw [if_pos hij]
    by_cases hb : key v < t.size
    · rw [if_pos hb]; rfl
    · exfalso
      have hn : t[j]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      unfold has at h; rw [hn] at h; simp at h
  · rw [if_neg hij]; exact h

theorem has_add_self {t : Marks} {v : List Bool} (h : key v < t.size) :
    has (add t v) (key v) = true := by
  unfold has add
  rw [Array.set!, Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]; rfl

def addAll (t : Marks) (l : List (List Bool)) : Marks := l.foldl add t

theorem size_addAll : ∀ (l : List (List Bool)) (t : Marks), (addAll t l).size = t.size := by
  intro l; induction l with
  | nil => intro t; rfl
  | cons v l ih => intro t; exact (ih (add t v)).trans (size_add t v)

theorem has_addAll_mono : ∀ (l : List (List Bool)) (t : Marks) (j : Nat),
    has t j = true → has (addAll t l) j = true := by
  intro l; induction l with
  | nil => intro t j h; exact h
  | cons v l ih => intro t j h; exact ih (add t v) j (has_add_mono h)

theorem has_addAll_of_mem : ∀ (l : List (List Bool)) (t : Marks) (v : List Bool),
    v ∈ l → key v < 65536 → t.size = 65536 → has (addAll t l) (key v) = true := by
  intro l; induction l with
  | nil => intro _ _ hm; exact absurd hm (by simp)
  | cons w l ih =>
    intro t v hm hk hsz
    rcases List.mem_cons.mp hm with h | h
    · subst h
      exact has_addAll_mono l (add t v) (key v) (has_add_self (by omega))
    · exact ih (add t w) v h hk (by rw [size_add, hsz])

def four (a b : List Bool) : List (List Bool) :=
  [tand false a false b, tand false a true b, tand true a false b, tand true a true b]

def combB (a : List Bool) (B : List (List Bool)) (t : Marks) : Marks :=
  B.foldl (fun t b => addAll t (four a b)) t

def combine (A B : List (List Bool)) (t : Marks) : Marks := A.foldl (fun t a => combB a B t) t

theorem size_combB (a : List Bool) : ∀ (B : List (List Bool)) (t : Marks),
    (combB a B t).size = t.size := by
  intro B; induction B with
  | nil => intro t; rfl
  | cons b B ih => intro t; exact (ih (addAll t (four a b))).trans (size_addAll _ t)

theorem has_combB_mono (a : List Bool) : ∀ (B : List (List Bool)) (t : Marks) (j : Nat),
    has t j = true → has (combB a B t) j = true := by
  intro B; induction B with
  | nil => intro t j h; exact h
  | cons b B ih => intro t j h; exact ih _ j (has_addAll_mono _ t j h)

theorem has_combB_of_mem (a : List Bool) : ∀ (B : List (List Bool)) (t : Marks)
    (b : List Bool) (w : List Bool), b ∈ B → w ∈ four a b → key w < 65536 → t.size = 65536 →
    has (combB a B t) (key w) = true := by
  intro B; induction B with
  | nil => intro _ _ _ hm; exact absurd hm (by simp)
  | cons b' B ih =>
    intro t b w hb hw hk hsz
    rcases List.mem_cons.mp hb with h | h
    · subst h
      exact has_combB_mono a B _ _ (has_addAll_of_mem (four a b) t w hw hk hsz)
    · exact ih (addAll t (four a b')) b w h hw hk (by rw [size_addAll, hsz])

theorem size_combine : ∀ (A B : List (List Bool)) (t : Marks), (combine A B t).size = t.size := by
  intro A; induction A with
  | nil => intro B t; rfl
  | cons a A ih => intro B t; exact (ih B (combB a B t)).trans (size_combB a B t)

theorem has_combine_mono : ∀ (A B : List (List Bool)) (t : Marks) (j : Nat),
    has t j = true → has (combine A B t) j = true := by
  intro A; induction A with
  | nil => intro B t j h; exact h
  | cons a A ih => intro B t j h; exact ih B _ j (has_combB_mono a B t j h)

theorem has_combine_of_mem : ∀ (A B : List (List Bool)) (t : Marks) (a b w : List Bool),
    a ∈ A → b ∈ B → w ∈ four a b → key w < 65536 → t.size = 65536 →
    has (combine A B t) (key w) = true := by
  intro A; induction A with
  | nil => intro _ _ _ _ _ hm; exact absurd hm (by simp)
  | cons a' A ih =>
    intro B t a b w ha hb hw hk hsz
    rcases List.mem_cons.mp ha with h | h
    · subst h
      exact has_combine_mono A B _ _ (has_combB_of_mem a B t b w hb hw hk hsz)
    · exact ih B (combB a' B t) a b w h hb hw hk (by rw [size_combB, hsz])

def present (t : Marks) : List (List Bool) :=
  (List.range 65536).filterMap (fun j => if has t j then some (unkey 16 j) else none)

def leavesT : List (List Bool) :=
  [tab (fun x => x 0), tab (fun x => x 1), tab (fun x => x 2), tab (fun x => x 3), tab (fun _ => true)]

def L0 : Marks := addAll emptyM leavesT

def stepF (prev : List Marks) (k : Nat) (t : Marks) (i : Nat) : Marks :=
  combine (present (prev.getD i emptyM)) (present (prev.getD (k - i) emptyM)) t

def stepL (prev : List Marks) (k : Nat) : Marks :=
  (List.range (k + 1)).foldl (stepF prev k) emptyM

def levels : Nat → List Marks
  | 0 => [L0]
  | k + 1 => let prev := levels k; prev ++ [stepL prev k]

def lvl : Nat → Marks
  | 0 => L0
  | k + 1 => stepL (levels k) k

theorem levels_length : ∀ k, (levels k).length = k + 1 := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => show ((levels k) ++ [stepL (levels k) k]).length = k + 2
                 simp [ih]

theorem getD_append_left {α} (l : List α) (x : α) (d : α) (j : Nat) (h : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  unfold List.getD
  rw [List.getElem?_append_left h]

theorem getD_append_right {α} (l : List α) (x : α) (d : α) :
    (l ++ [x]).getD l.length d = x := by
  unfold List.getD
  rw [List.getElem?_append_right (by omega)]
  simp

theorem lvl_succ_eq (k : Nat) : lvl (k + 1) = stepL (levels k) k := rfl

theorem getD_levels_self : ∀ k, (levels k).getD k emptyM = lvl k := by
  intro k; cases k with
  | zero => show List.getD [L0] 0 emptyM = L0
            simp [List.getD]
  | succ k =>
    have h := getD_append_right (levels k) (stepL (levels k) k) emptyM
    rw [levels_length] at h
    show ((levels k) ++ [stepL (levels k) k]).getD (k + 1) emptyM = _
    rw [h, lvl_succ_eq]

theorem getD_levels : ∀ k j, j ≤ k → (levels k).getD j emptyM = lvl j := by
  intro k; induction k with
  | zero => intro j hj; have h0 : j = 0 := by omega
            subst h0; exact getD_levels_self 0
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · show ((levels k) ++ [stepL (levels k) k]).getD j emptyM = lvl j
      rw [getD_append_left _ _ _ _ (by rw [levels_length]; omega)]
      exact ih j (by omega)
    · have hj' : j = k + 1 := by omega
      subst hj'; exact getD_levels_self (k + 1)

theorem length_unkey : ∀ n j, (unkey n j).length = n := by
  intro n; induction n with
  | zero => intro j; rfl
  | succ n ih => intro j; simp [unkey, ih]

theorem unkey_key : ∀ v : List Bool, unkey v.length (key v) = v := by
  intro v; induction v with
  | nil => rfl
  | cons b l ih =>
    have h2 : ((if b then 1 else 0) + 2 * key l) % 2 = (if b then 1 else 0) := by
      cases b <;> simp <;> omega
    have hd : ((if b then 1 else 0) + 2 * key l) / 2 = key l := by
      cases b <;> simp <;> omega
    simp only [List.length_cons, unkey, key, h2, hd, ih]
    cases b <;> simp

theorem key_lt : ∀ v : List Bool, key v < 2 ^ v.length := by
  intro v; induction v with
  | nil => simp [key]
  | cons b l ih =>
    have h : 2 ^ (b :: l).length = 2 * 2 ^ l.length := by
      simp [List.length_cons, Nat.pow_succ]; omega
    rw [h]; simp only [key]; cases b <;> simp <;> omega

theorem length_tab (f : Func 4) : (tab f).length = 16 := by simp [tab]

theorem key_tab_lt (f : Func 4) : key (tab f) < 65536 := by
  have h := key_lt (tab f)
  rw [length_tab] at h
  simpa using h

theorem mem_present {t : Marks} {v : List Bool} (hv : v.length = 16)
    (h : has t (key v) = true) : v ∈ present t := by
  refine List.mem_filterMap.mpr ⟨key v, ?_, ?_⟩
  · refine List.mem_range.mpr ?_
    have := key_lt v; rw [hv] at this; simpa using this
  · rw [if_pos h, ← hv, unkey_key]

theorem size_stepF (prev : List Marks) (k : Nat) (t : Marks) (i : Nat) :
    (stepF prev k t i).size = t.size := size_combine _ _ t

theorem has_stepF_mono {prev k t i j} (h : has t j = true) :
    has (stepF prev k t i) j = true := has_combine_mono _ _ t j h

theorem has_fold_mono : ∀ (L : List Nat) (prev : List Marks) (k : Nat) (t : Marks) (j : Nat),
    has t j = true → has (L.foldl (stepF prev k) t) j = true := by
  intro L; induction L with
  | nil => intro _ _ t j h; exact h
  | cons i L ih => intro prev k t j h; exact ih prev k _ j (has_stepF_mono h)

theorem size_fold : ∀ (L : List Nat) (prev : List Marks) (k : Nat) (t : Marks),
    (L.foldl (stepF prev k) t).size = t.size := by
  intro L; induction L with
  | nil => intro _ _ t; rfl
  | cons i L ih => intro prev k t; exact (ih prev k _).trans (size_stepF prev k t i)

theorem has_fold_hit : ∀ (L : List Nat) (prev : List Marks) (k : Nat) (t : Marks) (i : Nat)
    (a b w : List Bool), i ∈ L → a ∈ present (prev.getD i emptyM) →
    b ∈ present (prev.getD (k - i) emptyM) → w ∈ four a b → key w < 65536 → t.size = 65536 →
    has (L.foldl (stepF prev k) t) (key w) = true := by
  intro L; induction L with
  | nil => intro _ _ _ _ _ _ _ hi; exact absurd hi (by simp)
  | cons i' L ih =>
    intro prev k t i a b w hi ha hb hw hk hsz
    rcases List.mem_cons.mp hi with h | h
    · subst h
      exact has_fold_mono L prev k _ _ (has_combine_of_mem _ _ t a b w ha hb hw hk hsz)
    · exact ih prev k _ i a b w h ha hb hw hk (by rw [size_stepF, hsz])

theorem size_L0 : L0.size = 65536 := by
  rw [L0, size_addAll]; exact Array.size_replicate

theorem size_lvl : ∀ k, (lvl k).size = 65536 := by
  intro k
  cases k with
  | zero => exact size_L0
  | succ k => rw [lvl_succ_eq, stepL, size_fold]; exact Array.size_replicate

private theorem zipWith_map_map {α β γ δ} (f : β → γ → δ) (g : α → β) (h : α → γ) :
    ∀ l : List α, List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a)) := by
  intro l; induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem tab_and (pa pb : Bool) (a b : Frm 4) :
    tab (evalF (Frm.and pa a pb b)) = tand pa (tab (evalF a)) pb (tab (evalF b)) := by
  simp only [tab, tand, evalF, zipWith_map_map]

theorem size_emptyM : emptyM.size = 65536 := Array.size_replicate

theorem dp_complete : ∀ φ : Frm 4, has (lvl (gatesF φ)) (key (tab (evalF φ))) = true := by
  intro φ
  induction φ with
  | var i =>
    show has L0 (key (tab (fun x => x i))) = true
    refine has_addAll_of_mem leavesT emptyM _ ?_ (key_tab_lt _) size_emptyM
    match i with
    | ⟨0, _⟩ => exact List.mem_cons.mpr (Or.inl rfl)
    | ⟨1, _⟩ => simp [leavesT]
    | ⟨2, _⟩ => simp [leavesT]
    | ⟨3, _⟩ => simp [leavesT]
  | one =>
    show has L0 (key (tab (fun _ => true))) = true
    exact has_addAll_of_mem leavesT emptyM _ (by simp [leavesT]) (key_tab_lt _) size_emptyM
  | and pa a pb b iha ihb =>
    have hg : gatesF (Frm.and pa a pb b) = (gatesF a + gatesF b) + 1 := by
      simp only [gatesF]; omega
    rw [hg, lvl_succ_eq, stepL, tab_and]
    have hi : gatesF a ∈ List.range (gatesF a + gatesF b + 1) := by
      refine List.mem_range.mpr ?_; omega
    have hja : ((levels (gatesF a + gatesF b)).getD (gatesF a) emptyM) = lvl (gatesF a) := by
      exact getD_levels _ _ (by omega)
    have hjb : ((levels (gatesF a + gatesF b)).getD (gatesF a + gatesF b - gatesF a) emptyM)
        = lvl (gatesF b) := by
      have he : gatesF a + gatesF b - gatesF a = gatesF b := by omega
      rw [he]; exact getD_levels _ _ (by omega)
    refine has_fold_hit _ _ _ _ (gatesF a) (tab (evalF a)) (tab (evalF b)) _ hi ?_ ?_ ?_ ?_ size_emptyM
    · rw [hja]; exact mem_present (length_tab _) iha
    · rw [hjb]; exact mem_present (length_tab _) ihb
    · cases pa <;> cases pb <;> simp [four]
    · rw [← tab_and]; exact key_tab_lt _

def z03de : Func 4 := fun x => (0x03de >>> idx x) % 2 == 1

def phi7 : Frm 4 :=
  Frm.and true (Frm.and true (Frm.var 1) false (Frm.and true (Frm.var 2) true
    (Frm.and true (Frm.var 0) true (Frm.var 3)))) true (Frm.and true (Frm.var 3) true
    (Frm.and true (Frm.var 1) true (Frm.and true (Frm.var 0) false (Frm.var 2))))

theorem phi7_gates : gatesF phi7 = 7 := by decide

theorem phi7_computes : FormulaComputes phi7 z03de :=
  Or.inr (funext16' (by decide))

theorem z03de_hasFormula7 : HasFormula z03de 7 :=
  ⟨phi7, Nat.le_of_eq phi7_gates, phi7_computes⟩

theorem testBit_key : ∀ (l : List Bool) (i : Nat), (key l).testBit i = l.getD i false := by
  intro l
  induction l with
  | nil => intro i; simp [key, Nat.testBit]
  | cons b l ih =>
    intro i
    cases i with
    | zero =>
      simp only [key, Nat.testBit_zero, List.getD, List.getElem?_cons_zero, Option.getD]
      cases b <;> simp <;> omega
    | succ i =>
      have hd : ((if b then 1 else 0) + 2 * key l) / 2 = key l := by cases b <;> simp <;> omega
      simp only [key, Nat.testBit_succ, hd, ih i]
      simp [List.getD]

def ttN (f : Func 4) : Nat := key (tab f)

theorem testBit_ttN (f : Func 4) (t : Nat) (ht : t < 16) : (ttN f).testBit t = f (asg t) := by
  rw [ttN, testBit_key]
  simp only [tab, List.getD]
  rw [List.getElem?_map, List.getElem?_range ht]
  rfl

def cmask : Nat := 65535

theorem testBit_cmask : ∀ t, t < 16 → cmask.testBit t = true := by decide

def nnot (b : Bool) (v : Nat) : Nat := if b then v ^^^ cmask else v

theorem testBit_nnot (b : Bool) (v t : Nat) (ht : t < 16) :
    (nnot b v).testBit t = xor b (v.testBit t) := by
  cases b <;> simp [nnot, Nat.testBit_xor, testBit_cmask t ht]

def gAnd (na : Bool) (a : Nat) (nb : Bool) (b : Nat) : Nat := nnot na a &&& nnot nb b

theorem testBit_gAnd (na : Bool) (a : Nat) (nb : Bool) (b t : Nat) (ht : t < 16) :
    (gAnd na a nb b).testBit t = (xor na (a.testBit t) && xor nb (b.testBit t)) := by
  rw [gAnd, Nat.testBit_and, testBit_nnot na a t ht, testBit_nnot nb b t ht]

def inTT (i : Nat) : Nat :=
  if i = 0 then 0xAAAA else if i = 1 then 0xCCCC else if i = 2 then 0xF0F0 else 0xFF00

theorem testBit_inTT : ∀ (i : Fin 4) (t : Nat), t < 16 → (inTT i.val).testBit t = asg t i := by
  decide

def wAt (acc : List Nat) (w : Nat) : Nat := if w < 4 then inTT w else acc.getD (w - 4) 0

def ttsOf (gs : List Gate) : List Nat :=
  gs.foldl (fun acc g => acc ++ [gAnd g.na (wAt acc g.ia) g.nb (wAt acc g.ib)]) []

private theorem length_fold : ∀ (gs : List Gate) (acc : List Nat),
    (gs.foldl (fun acc g => acc ++ [gAnd g.na (wAt acc g.ia) g.nb (wAt acc g.ib)]) acc).length
      = acc.length + gs.length := by
  intro gs; induction gs with
  | nil => intro acc; simp
  | cons g gs ih => intro acc; simp only [List.foldl_cons, ih, List.length_append]; simp; omega

theorem length_ttsOf (gs : List Gate) : (ttsOf gs).length = gs.length := by
  have := length_fold gs []; simpa [ttsOf] using this

theorem ttsOf_concat (gs : List Gate) (g : Gate) :
    ttsOf (gs ++ [g])
      = ttsOf gs ++ [gAnd g.na (wAt (ttsOf gs) g.ia) g.nb (wAt (ttsOf gs) g.ib)] := by
  simp [ttsOf, List.foldl_append]

theorem evalGates_concat (x : Assign 4) (gs : List Gate) (g : Gate) :
    evalGates x (gs ++ [g]) = gstep x (evalGates x gs) g := by
  rw [evalGates_foldl, List.foldl_append, evalGates_foldl]
  simp

private theorem getD_push_lt (V : Array Bool) (b : Bool) (p : Nat) (h : p < V.size) :
    (V.push b).getD p false = V.getD p false := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    if_neg (by omega : ¬ (p = V.size))]

private theorem getD_push_self (V : Array Bool) (b : Bool) :
    (V.push b).getD V.size false = b := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos rfl]; rfl

theorem wfC_concat_left4 (gs : List Gate) (g : Gate) (h : wfC 4 (gs ++ [g])) : wfC 4 gs := by
  intro p
  have hp : p.val < (gs ++ [g]).length := by
    have := p.isLt; simp only [List.length_append, List.length_singleton]; omega
  have := h ⟨p.val, hp⟩
  simpa [List.get_eq_getElem, List.getElem_append_left p.isLt] using this

private theorem testBit_ttsOf_aux (t : Nat) (ht : t < 16) : ∀ (L : Nat) (gs : List Gate),
    gs.length ≤ L → wfC 4 gs → ∀ p, p < gs.length →
      ((ttsOf gs).getD p 0).testBit t = (evalGates (asg t) gs).getD p false := by
  intro L
  induction L with
  | zero => intro gs hL _ p hp; omega
  | succ L ih =>
    intro gs hL hwf p hp
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil; simp at hp
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hwf' : wfC 4 gs' := wfC_concat_left4 gs' g hwf
      have hlen : (gs' ++ [g]).length = gs'.length + 1 := by simp
      have hL' : gs'.length ≤ L := by omega
      have hwire : ∀ w, w < 4 + gs'.length →
          (wAt (ttsOf gs') w).testBit t = wireVal (asg t) (evalGates (asg t) gs') w := by
        intro w hw
        by_cases h4 : w < 4
        · rw [wAt, if_pos h4]
          have hv : wireVal (asg t) (evalGates (asg t) gs') w = asg t ⟨w, h4⟩ := by
            simp only [wireVal, dif_pos h4]
          rw [hv]
          exact testBit_inTT ⟨w, h4⟩ t ht
        · rw [wAt, if_neg h4]
          have hlt : w - 4 < gs'.length := by omega
          rw [ih gs' hL' hwf' (w - 4) hlt]
          simp only [wireVal, dif_neg h4]
      rcases Nat.lt_or_ge p gs'.length with hlt | hge
      · rw [ttsOf_concat, getD_append_left _ _ _ _ (by rw [length_ttsOf]; omega),
          evalGates_concat, gstep,
          getD_push_lt _ _ _ (by rw [size_evalGates]; omega)]
        exact ih gs' hL' hwf' p hlt
      · have hpe : p = gs'.length := by omega
        subst hpe
        have hg : (gs' ++ [g])[gs'.length] = g := by
          simp [List.getElem_append_right]
        have hbound := hwf ⟨gs'.length, by omega⟩
        rw [List.get_eq_getElem] at hbound
        simp only [hg] at hbound
        rw [ttsOf_concat]
        have h1 := getD_append_right (ttsOf gs')
          (gAnd g.na (wAt (ttsOf gs') g.ia) g.nb (wAt (ttsOf gs') g.ib)) 0
        rw [length_ttsOf] at h1
        rw [h1, evalGates_concat, gstep]
        have hsz : (evalGates (asg t) gs').size = gs'.length := size_evalGates _ _
        have h2 := getD_push_self (evalGates (asg t) gs')
          ((xor g.na (wireVal (asg t) (evalGates (asg t) gs') g.ia)) &&
            (xor g.nb (wireVal (asg t) (evalGates (asg t) gs') g.ib)))
        rw [hsz] at h2
        rw [h2, testBit_gAnd _ _ _ _ _ ht, hwire g.ia hbound.1, hwire g.ib hbound.2]

theorem testBit_ttsOf (t : Nat) (ht : t < 16) (gs : List Gate) (hwf : wfC 4 gs)
    (p : Nat) (hp : p < gs.length) :
    ((ttsOf gs).getD p 0).testBit t = (evalGates (asg t) gs).getD p false :=
  testBit_ttsOf_aux t ht gs.length gs (Nat.le_refl _) hwf p hp

def wireCount (acc : List Nat) : Nat := 4 + acc.length

def optsAt (acc : List Nat) : List (Gate × Nat) :=
  (List.range (wireCount acc)).flatMap (fun a =>
    ((List.range (wireCount acc)).filter (fun b => decide (a ≤ b))).flatMap (fun b =>
      [ (⟨false, a, false, b⟩, gAnd false (wAt acc a) false (wAt acc b)),
        (⟨false, a, true , b⟩, gAnd false (wAt acc a) true  (wAt acc b)),
        (⟨true , a, false, b⟩, gAnd true  (wAt acc a) false (wAt acc b)),
        (⟨true , a, true , b⟩, gAnd true  (wAt acc a) true  (wAt acc b)) ]))

theorem mem_optsAt (acc : List Nat) (na nb : Bool) (a b : Nat)
    (ha : a < wireCount acc) (hb : b < wireCount acc) (hab : a ≤ b) :
    ((⟨na, a, nb, b⟩ : Gate), gAnd na (wAt acc a) nb (wAt acc b)) ∈ optsAt acc := by
  refine List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr hb, by simpa using hab⟩
  · cases na <;> cases nb <;> simp

def redundant (acc : List Nat) (v : Nat) : Bool :=
  v == 0 || v == cmask ||
    (List.range (wireCount acc)).any (fun w => (wAt acc w == v) || (nnot true (wAt acc w) == v))

def anyC : Nat → List Nat → Nat → Bool
  | 0, _, _ => false
  | 1, acc, tgt => (optsAt acc).any (fun gv => gv.2 == tgt || gv.2 == nnot true tgt)
  | k + 2, acc, tgt =>
      (optsAt acc).any (fun gv => !redundant acc gv.2 && anyC (k + 1) (acc ++ [gv.2]) tgt)

def NormFrom : List Gate → List Gate → Prop
  | _, [] => True
  | _, [g] => g.ia ≤ g.ib
  | pre, g :: rest =>
      g.ia ≤ g.ib
      ∧ redundant (ttsOf pre)
          (gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) = false
      ∧ NormFrom (pre ++ [g]) rest

theorem wfC_head (pre : List Gate) (g : Gate) (rest : List Gate)
    (hwf : wfC 4 (pre ++ g :: rest)) : g.ia < 4 + pre.length ∧ g.ib < 4 + pre.length := by
  have hlt : pre.length < (pre ++ g :: rest).length := by simp
  have h := hwf ⟨pre.length, hlt⟩
  rw [List.get_eq_getElem] at h
  have hg : (pre ++ g :: rest)[pre.length] = g := by
    rw [List.getElem_append_right (by omega)]
    simp
  rw [hg] at h
  exact h

theorem last_tt (pre : List Gate) (g : Gate) :
    (ttsOf (pre ++ [g])).getD ((pre ++ [g]).length - 1) 0
      = gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib) := by
  have h1 := getD_append_right (ttsOf pre)
    (gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) 0
  rw [length_ttsOf] at h1
  rw [ttsOf_concat]
  have h2 : (pre ++ [g]).length - 1 = pre.length := by simp
  rw [h2, h1]

theorem anyC_of_norm : ∀ (suf pre : List Gate) (tgt : Nat),
    wfC 4 (pre ++ suf) → suf ≠ [] → NormFrom pre suf →
    ((ttsOf (pre ++ suf)).getD ((pre ++ suf).length - 1) 0 = tgt
      ∨ (ttsOf (pre ++ suf)).getD ((pre ++ suf).length - 1) 0 = nnot true tgt) →
    anyC suf.length (ttsOf pre) tgt = true := by
  intro suf
  induction suf with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons g rest ih =>
    intro pre tgt hwf _ hnorm hval
    have hb := wfC_head pre g rest hwf
    have hlen : (ttsOf pre).length = pre.length := length_ttsOf pre
    have hmem : ((⟨g.na, g.ia, g.nb, g.ib⟩ : Gate),
        gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) ∈ optsAt (ttsOf pre) := by
      refine mem_optsAt (ttsOf pre) g.na g.nb g.ia g.ib ?_ ?_ ?_
      · rw [wireCount, hlen]; exact hb.1
      · rw [wireCount, hlen]; exact hb.2
      · cases rest with
        | nil => exact hnorm
        | cons g2 r2 => exact hnorm.1
    cases rest with
    | nil =>
      rw [last_tt pre g] at hval
      show (optsAt (ttsOf pre)).any _ = true
      refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
      rcases hval with h | h
      · simp [h]
      · simp [h]
    | cons g2 r2 =>
      obtain ⟨-, hred, hnorm'⟩ := hnorm
      have hcat : pre ++ g :: g2 :: r2 = (pre ++ [g]) ++ (g2 :: r2) := by simp
      show (optsAt (ttsOf pre)).any _ = true
      refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
      have hih := ih (pre ++ [g]) tgt (by rw [← hcat]; exact hwf) (by simp) hnorm'
        (by rw [← hcat] at *; exact hval)
      rw [ttsOf_concat] at hih
      simp only [List.length_cons] at hih
      simp only [hred, Bool.not_false, Bool.true_and]
      exact hih

private theorem ttsOf_append_aux : ∀ (L : Nat) (suf pre : List Gate) (p : Nat),
    suf.length ≤ L → p < pre.length →
    (ttsOf (pre ++ suf)).getD p 0 = (ttsOf pre).getD p 0 := by
  intro L
  induction L with
  | zero =>
    intro suf pre p hL hp
    have : suf = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp
  | succ L ih =>
    intro suf pre p hL hp
    rcases List.eq_nil_or_concat suf with hnil | ⟨suf', g, hcat⟩
    · subst hnil; simp
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hc2 : pre ++ (suf' ++ [g]) = (pre ++ suf') ++ [g] := by simp
      rw [hc2, ttsOf_concat,
        getD_append_left _ _ _ _ (by rw [length_ttsOf, List.length_append]; omega)]
      exact ih suf' pre p (by simp at hL; omega) hp

theorem ttsOf_append_getD (suf pre : List Gate) (p : Nat) (hp : p < pre.length) :
    (ttsOf (pre ++ suf)).getD p 0 = (ttsOf pre).getD p 0 :=
  ttsOf_append_aux suf.length suf pre p (Nat.le_refl _) hp

theorem ttsOf_head (pre : List Gate) (g : Gate) (rest : List Gate) :
    (ttsOf (pre ++ g :: rest)).getD pre.length 0
      = gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib) := by
  have hcat : pre ++ g :: rest = (pre ++ [g]) ++ rest := by simp
  rw [hcat, ttsOf_append_getD rest (pre ++ [g]) pre.length (by simp)]
  have h := last_tt pre g
  simpa using h

theorem testBit_wAt (t : Nat) (ht : t < 16) (gs : List Gate) (hwf : wfC 4 gs)
    (w : Nat) (hw : w < 4 + gs.length) :
    (wAt (ttsOf gs) w).testBit t = wireVal (asg t) (evalGates (asg t) gs) w := by
  by_cases h4 : w < 4
  · rw [wAt, if_pos h4]
    have hv : wireVal (asg t) (evalGates (asg t) gs) w = asg t ⟨w, h4⟩ := by
      simp only [wireVal, dif_pos h4]
    rw [hv]
    exact testBit_inTT ⟨w, h4⟩ t ht
  · rw [wAt, if_neg h4, testBit_ttsOf t ht gs hwf (w - 4) (by omega)]
    simp only [wireVal, dif_neg h4]

theorem exists_row (x : Assign 4) : ∃ t, t < 16 ∧ asg t = x := ⟨idx x, idx_lt x, asg_idx x⟩

theorem isConstGate_of_tt (gs : List Gate) (hwf : wfC 4 gs) (p : Nat) (hp : p < gs.length)
    (c : Bool) (h : ∀ t, t < 16 → ((ttsOf gs).getD p 0).testBit t = c) :
    IsConstGate 4 gs p c := by
  intro x
  obtain ⟨t, ht, hx⟩ := exists_row x
  subst hx
  rw [← testBit_ttsOf t ht gs hwf p hp]
  exact h t ht

theorem isPassThrough_of_tt (gs : List Gate) (hwf : wfC 4 gs) (p : Nat) (hp : p < gs.length)
    (w : Nat) (hw : w < 4 + gs.length) (inv : Bool)
    (h : (ttsOf gs).getD p 0 = nnot inv (wAt (ttsOf gs) w)) :
    IsPassThroughAt 4 gs p w inv := by
  intro x
  obtain ⟨t, ht, hx⟩ := exists_row x
  subst hx
  rw [← testBit_ttsOf t ht gs hwf p hp, h, testBit_nnot inv _ t ht,
    testBit_wAt t ht gs hwf w hw]

theorem wAt_prefix (pre suf : List Gate) (w : Nat) (hw : w < 4 + pre.length) :
    wAt (ttsOf pre) w = wAt (ttsOf (pre ++ suf)) w := by
  by_cases h4 : w < 4
  · simp [wAt, h4]
  · rw [wAt, wAt, if_neg h4, if_neg h4, ttsOf_append_getD suf pre (w - 4) (by omega)]

private theorem redundant_false_gen (gs pre : List Gate) (v : Nat) (hwf : wfC 4 gs)
    (hp : pre.length < gs.length)
    (hgetp : (ttsOf gs).getD pre.length 0 = v)
    (hwe : ∀ w, w < 4 + pre.length → wAt (ttsOf gs) w = wAt (ttsOf pre) w)
    (hnoconst : ∀ c, ¬ IsConstGate 4 gs pre.length c)
    (hnopt : ∀ w inv, w < 4 + pre.length → ¬ IsPassThroughAt 4 gs pre.length w inv) :
    redundant (ttsOf pre) v = false := by
  cases htrue : redundant (ttsOf pre) v with
  | false => rfl
  | true =>
  exfalso
  rw [redundant, Bool.or_eq_true, Bool.or_eq_true] at htrue
  rcases htrue with (hz | hcm) | hany
  · refine hnoconst false (isConstGate_of_tt gs hwf pre.length hp false (fun t ht => ?_))
    rw [hgetp, of_decide_eq_true hz]; simp
  · refine hnoconst true (isConstGate_of_tt gs hwf pre.length hp true (fun t ht => ?_))
    rw [hgetp, of_decide_eq_true hcm]; exact testBit_cmask t ht
  · obtain ⟨w, hwmem, hw⟩ := List.any_eq_true.mp hany
    have hwlt : w < 4 + pre.length := by
      have h := List.mem_range.mp hwmem
      rw [wireCount, length_ttsOf] at h
      exact h
    have hwgs : w < 4 + gs.length := by omega
    rcases (Bool.or_eq_true _ _).mp hw with h | h
    · refine hnopt w false hwlt (isPassThrough_of_tt gs hwf pre.length hp w hwgs false ?_)
      rw [hgetp, hwe w hwlt, nnot]
      exact (of_decide_eq_true h).symm
    · refine hnopt w true hwlt (isPassThrough_of_tt gs hwf pre.length hp w hwgs true ?_)
      rw [hgetp, hwe w hwlt]
      exact (of_decide_eq_true h).symm

theorem redundant_false (f : Func 4) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC 4 gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (pre : List Gate) (g : Gate) (rest : List Gate) (hcat : gs = pre ++ g :: rest)
    (hrest : rest ≠ []) :
    redundant (ttsOf pre)
      (gAnd g.na (wAt (ttsOf pre) g.ia) g.nb (wAt (ttsOf pre) g.ib)) = false := by
  have hlen2 : gs.length = pre.length + rest.length + 1 := by
    rw [hcat]; simp; omega
  have hr1 : 1 ≤ rest.length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  refine redundant_false_gen gs pre _ hwf (by omega) ?_ ?_ ?_ ?_
  · rw [hcat]; exact ttsOf_head pre g rest
  · intro w hw
    rw [hcat]; exact (wAt_prefix pre (g :: rest) w hw).symm
  · intro c hcst
    exact opt_no_const_gate 4 f gs m h0 h1 hwf hopt hlen hc pre.length (by omega) c hcst
  · intro w inv hwlt hpt
    exact opt_no_passthrough 4 f gs m hwf hopt hlen hc pre.length w inv (by omega) hwlt
      (Or.inr (by omega)) hpt

def normGate (g : Gate) : Gate := if g.ia ≤ g.ib then g else ⟨g.nb, g.ib, g.na, g.ia⟩
def normC (gs : List Gate) : List Gate := gs.map normGate

theorem gAnd_comm (na : Bool) (a : Nat) (nb : Bool) (b : Nat) : gAnd na a nb b = gAnd nb b na a := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  rw [gAnd, gAnd, Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

theorem length_normC (gs : List Gate) : (normC gs).length = gs.length := by simp [normC]

theorem mem_normC_le (gs : List Gate) : ∀ g ∈ normC gs, g.ia ≤ g.ib := by
  intro g hg
  obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
  rw [normGate]
  by_cases h : g0.ia ≤ g0.ib
  · simp [h]
  · simp only [h, if_false]
    omega

theorem normC_concat (gs : List Gate) (g : Gate) :
    normC (gs ++ [g]) = normC gs ++ [normGate g] := by simp [normC]

theorem wfC_normC (gs : List Gate) (hwf : wfC 4 gs) : wfC 4 (normC gs) := by
  intro p
  have hp : p.val < gs.length := by
    have h := p.isLt; simp only [length_normC] at h; exact h
  have h := hwf ⟨p.val, hp⟩
  rw [List.get_eq_getElem] at h ⊢
  have hg : (normC gs)[p.val] = normGate gs[p.val] := by
    simp only [normC]
    rw [List.getElem_map]
  rw [hg, normGate]
  by_cases hle : (gs[p.val]).ia ≤ (gs[p.val]).ib
  · simpa [hle] using h
  · simp only [hle, if_false]
    exact ⟨h.2, h.1⟩

private theorem evalGates_normC_aux : ∀ (L : Nat) (gs : List Gate) (x : Assign 4),
    gs.length ≤ L → evalGates x (normC gs) = evalGates x gs := by
  intro L
  induction L with
  | zero =>
    intro gs x hL
    have : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ L ih =>
    intro gs x hL
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil; rfl
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hL' : gs'.length ≤ L := by simp at hL; omega
      rw [normC_concat, evalGates_concat, evalGates_concat, ih gs' x hL', gstep, gstep, normGate]
      by_cases hle : g.ia ≤ g.ib
      · simp [hle]
      · simp only [hle, if_false]
        rw [Bool.and_comm]

theorem evalGates_normC (x : Assign 4) (gs : List Gate) :
    evalGates x (normC gs) = evalGates x gs :=
  evalGates_normC_aux gs.length gs x (Nat.le_refl _)

theorem circuitComputes_normC (gs : List Gate) (f : Func 4) (hc : CircuitComputes gs f) :
    CircuitComputes (normC gs) f := by
  have hout : ∀ x : Assign 4, circuitOut x (normC gs) = circuitOut x gs := by
    intro x
    rw [circuitOut, circuitOut, evalGates_normC, length_normC]
  rcases hc with h | h
  · exact Or.inl (fun x => by rw [hout x]; exact h x)
  · exact Or.inr (fun x => by rw [hout x]; exact h x)

private theorem ttsOf_normC_aux : ∀ (L : Nat) (gs : List Gate), gs.length ≤ L →
    ttsOf (normC gs) = ttsOf gs := by
  intro L
  induction L with
  | zero =>
    intro gs hL
    have : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ L ih =>
    intro gs hL
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil; rfl
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hL' : gs'.length ≤ L := by simp at hL; omega
      rw [normC_concat, ttsOf_concat, ttsOf_concat, ih gs' hL', normGate]
      by_cases hle : g.ia ≤ g.ib
      · simp [hle]
      · simp only [hle, if_false]
        rw [gAnd_comm]

theorem ttsOf_normC (gs : List Gate) : ttsOf (normC gs) = ttsOf gs :=
  ttsOf_normC_aux gs.length gs (Nat.le_refl _)

def Low (v : Nat) : Prop := ∀ t, 16 ≤ t → v.testBit t = false

theorem Low_of_lt (v : Nat) (h : v < 65536) : Low v := by
  intro t ht
  refine Nat.testBit_lt_two_pow ?_
  have h1 : (2:Nat) ^ 16 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  have h2 : (2:Nat) ^ 16 = 65536 := by rfl
  omega

theorem Low_zero : Low 0 := Low_of_lt 0 (by omega)

theorem inTT_lt : ∀ w, inTT w < 65536
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | (n + 3) => by simp [inTT]

theorem Low_nnot (b : Bool) (v : Nat) (hv : Low v) : Low (nnot b v) := by
  intro t ht
  cases b
  · exact hv t ht
  · rw [nnot, if_pos rfl, Nat.testBit_xor, hv t ht,
      Low_of_lt cmask (by rw [cmask]; omega) t ht]
    rfl

theorem Low_gAnd (na : Bool) (a : Nat) (nb : Bool) (b : Nat) (ha : Low a) (_hb : Low b) :
    Low (gAnd na a nb b) := by
  intro t ht
  rw [gAnd, Nat.testBit_and, Low_nnot na a ha t ht]
  rfl

theorem Low_key : ∀ (l : List Bool), l.length ≤ 16 → Low (key l) := by
  intro l hl t ht
  rw [testBit_key]
  have hn : l[t]? = none := List.getElem?_eq_none (by omega)
  simp [List.getD, hn]

theorem Low_ttN (f : Func 4) : Low (ttN f) := by
  refine Low_key (tab f) ?_
  rw [length_tab]
  omega

private theorem low_ttsOf_aux : ∀ (L : Nat) (gs : List Gate) (p : Nat), gs.length ≤ L →
    Low ((ttsOf gs).getD p 0) := by
  intro L
  induction L with
  | zero =>
    intro gs p hL
    have : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simpa [ttsOf] using Low_zero
  | succ L ih =>
    intro gs p hL
    rcases List.eq_nil_or_concat gs with hnil | ⟨gs', g, hcat⟩
    · subst hnil; simpa [ttsOf] using Low_zero
    · rw [List.concat_eq_append] at hcat
      subst hcat
      have hL' : gs'.length ≤ L := by simp at hL; omega
      rw [ttsOf_concat]
      rcases Nat.lt_or_ge p (ttsOf gs').length with hlt | hge
      · rw [getD_append_left _ _ _ _ hlt]; exact ih gs' p hL'
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · rw [← heq, getD_append_right]
          refine Low_gAnd _ _ _ _ ?_ ?_ <;>
            · rw [wAt]
              split
              · exact Low_of_lt _ (inTT_lt _)
              · exact ih gs' _ hL'
        · have hout : (ttsOf gs' ++ [gAnd g.na (wAt (ttsOf gs') g.ia) g.nb
              (wAt (ttsOf gs') g.ib)]).getD p 0 = 0 := by
            rw [List.getD, List.getElem?_eq_none (by simp; omega)]
            rfl
          rw [hout]; exact Low_zero

theorem low_ttsOf (gs : List Gate) (p : Nat) : Low ((ttsOf gs).getD p 0) :=
  low_ttsOf_aux gs.length gs p (Nat.le_refl _)

theorem eq_of_low (a b : Nat) (ha : Low a) (hb : Low b)
    (h : ∀ t, t < 16 → a.testBit t = b.testBit t) : a = b := by
  refine Nat.eq_of_testBit_eq (fun t => ?_)
  rcases Nat.lt_or_ge t 16 with hlt | hge
  · exact h t hlt
  · rw [ha t hge, hb t hge]

namespace DP4K
set_option maxRecDepth 100000
open ThresholdTree Witness4

def cmpl (v : Nat) : Nat := v ^^^ 65535
def mem (S g : Nat) : Bool := S.testBit g
def ins (S g : Nat) : Nat := S ||| (1 <<< g)
def leaves : List Nat := [0xAAAA, 0xCCCC, 0xF0F0, 0xFF00, 0xFFFF]
def L0M : Nat := leaves.foldl ins 0

def memb : Nat → Nat → Nat → List Nat → List Nat
  | 0, lo, S, acc => if S == 0 then acc else lo :: acc
  | d + 1, lo, S, acc =>
    if S == 0 then acc else
      memb d lo (S &&& ((1 <<< (2 ^ d)) - 1)) (memb d (lo + 2 ^ d) (S >>> (2 ^ d)) acc)

def members (S : Nat) : List Nat := memb 16 0 S []

def prodInto (acc : Nat) (A B : List Nat) : Nat :=
  A.foldl (fun acc a => B.foldl (fun acc b => ins acc (a &&& b)) acc) acc

def stepM (cs : List (List Nat)) (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun acc i => prodInto acc (cs.getD i []) (cs.getD (k - i) [])) 0

def zT : Nat := 0x03de

def closeM (m : Nat) : Nat := (members m).foldl (fun acc v => ins acc (cmpl v)) m

def build2 : Nat → List (Nat × List Nat)
  | 0 => [(L0M, members (closeM L0M))]
  | k + 1 =>
    let prev := build2 k
    let m := stepM (prev.map Prod.snd) k
    prev ++ [(m, members (closeM m))]

def hitNext (cs : List (List Nat)) (k z : Nat) : Bool :=
  (List.range (k + 1)).any fun i =>
    (cs.getD i []).any fun a =>
      (a &&& z == z || a &&& cmpl z == cmpl z) &&
        (cs.getD (k - i) []).any fun b => a &&& b == z || a &&& b == cmpl z

def miss2Of (z K : Nat) : Bool :=
  let l := build2 (K - 1)
  l.all (fun p => !mem p.1 z && !mem p.1 (cmpl z)) && !hitNext (l.map Prod.snd) (K - 1) z

def miss2 (K : Nat) : Bool := miss2Of zT K

theorem miss2_6 : miss2 6 = true := by decide +kernel

theorem mem_ins_of_mem {S h : Nat} (g : Nat) (hS : mem S h = true) : mem (ins S g) h = true := by
  simp only [mem, ins, Nat.testBit_or] at *; simp [hS]

theorem mem_ins_self (S g : Nat) : mem (ins S g) g = true := by
  simp only [mem, ins, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]

theorem prodB_mono (a : Nat) : ∀ (B : List Nat) (acc h : Nat), mem acc h = true →
    mem (B.foldl (fun acc b => ins acc (a &&& b)) acc) h = true := by
  intro B; induction B with
  | nil => intro acc h hm; exact hm
  | cons b B ih => intro acc h hm; exact ih _ h (mem_ins_of_mem _ hm)

theorem prodB_hit (a : Nat) : ∀ (B : List Nat) (acc b : Nat), b ∈ B →
    mem (B.foldl (fun acc b => ins acc (a &&& b)) acc) (a &&& b) = true := by
  intro B; induction B with
  | nil => intro _ _ hb; exact absurd hb (by simp)
  | cons b' B ih =>
    intro acc b hb
    rcases List.mem_cons.mp hb with h | h
    · subst h; exact prodB_mono a B _ _ (mem_ins_self _ _)
    · exact ih _ b h

theorem prodInto_mono : ∀ (A B : List Nat) (acc h : Nat), mem acc h = true →
    mem (prodInto acc A B) h = true := by
  intro A; induction A with
  | nil => intro B acc h hm; exact hm
  | cons a A ih => intro B acc h hm; exact ih B _ h (prodB_mono a B acc h hm)

theorem prodInto_hit : ∀ (A B : List Nat) (acc a b : Nat), a ∈ A → b ∈ B →
    mem (prodInto acc A B) (a &&& b) = true := by
  intro A; induction A with
  | nil => intro _ _ _ _ ha; exact absurd ha (by simp)
  | cons a' A ih =>
    intro B acc a b ha hb
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact prodInto_mono A B _ _ (prodB_hit a B acc b hb)
    · exact ih B _ a b h hb

theorem stepM_fold_mono (cs : List (List Nat)) (k : Nat) : ∀ (L : List Nat) (acc h : Nat),
    mem acc h = true →
    mem (L.foldl (fun acc i => prodInto acc (cs.getD i []) (cs.getD (k - i) [])) acc) h = true := by
  intro L; induction L with
  | nil => intro acc h hm; exact hm
  | cons i L ih => intro acc h hm; exact ih _ h (prodInto_mono _ _ _ _ hm)

theorem stepM_fold_hit (cs : List (List Nat)) (k : Nat) : ∀ (L : List Nat) (acc i a b : Nat),
    i ∈ L → a ∈ cs.getD i [] → b ∈ cs.getD (k - i) [] →
    mem (L.foldl (fun acc i => prodInto acc (cs.getD i []) (cs.getD (k - i) [])) acc) (a &&& b)
      = true := by
  intro L; induction L with
  | nil => intro _ _ _ _ hi; exact absurd hi (by simp)
  | cons i' L ih =>
    intro acc i a b hi ha hb
    rcases List.mem_cons.mp hi with h | h
    · subst h; exact stepM_fold_mono cs k L _ _ (prodInto_hit _ _ acc a b ha hb)
    · exact ih _ i a b h ha hb

theorem stepM_hit (cs : List (List Nat)) (k i a b : Nat) (hi : i ≤ k)
    (ha : a ∈ cs.getD i []) (hb : b ∈ cs.getD (k - i) []) : mem (stepM cs k) (a &&& b) = true :=
  stepM_fold_hit cs k _ 0 i a b (List.mem_range.mpr (by omega)) ha hb

theorem memb_mono : ∀ (d lo S : Nat) (acc : List Nat) (x : Nat), x ∈ acc → x ∈ memb d lo S acc := by
  intro d; induction d with
  | zero => intro lo S acc x hx; simp only [memb]; split <;> simp [hx]
  | succ d ih =>
    intro lo S acc x hx; simp only [memb]; split
    · exact hx
    · exact ih _ _ _ x (ih _ _ _ x hx)

theorem memb_complete : ∀ (d lo S : Nat) (acc : List Nat) (v : Nat), v < 2 ^ d →
    S.testBit v = true → lo + v ∈ memb d lo S acc := by
  intro d; induction d with
  | zero =>
    intro lo S acc v hv hb
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    have hS : (S == 0) = false := by
      cases h : (S == 0)
      · rfl
      · rw [beq_iff_eq.mp h] at hb; simp at hb
    simp [memb, hS]
  | succ d ih =>
    intro lo S acc v hv hb
    have hS : (S == 0) = false := by
      cases h : (S == 0)
      · rfl
      · rw [beq_iff_eq.mp h] at hb; simp at hb
    simp only [memb, hS]
    have hp : (2:Nat) ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    have hmask : (1 <<< (2 ^ d)) - 1 = 2 ^ (2 ^ d) - 1 := by rw [Nat.one_shiftLeft]
    rcases Nat.lt_or_ge v (2 ^ d) with hlt | hge
    · refine ih lo _ _ v hlt ?_
      rw [hmask, Nat.testBit_and, Nat.testBit_two_pow_sub_one, hb]
      simp only [Bool.true_and, decide_eq_true_eq]
      exact hlt
    · have hv' : v - 2 ^ d < 2 ^ d := by omega
      have hb' : (S >>> (2 ^ d)).testBit (v - 2 ^ d) = true := by
        rw [Nat.testBit_shiftRight]; rw [show 2 ^ d + (v - 2 ^ d) = v by omega]; exact hb
      have h1 := ih (lo + 2 ^ d) (S >>> (2 ^ d)) acc (v - 2 ^ d) hv' hb'
      rw [show lo + 2 ^ d + (v - 2 ^ d) = lo + v by omega] at h1
      exact memb_mono d lo _ _ _ h1

theorem members_complete (S v : Nat) (hv : v < 65536) (hb : mem S v = true) : v ∈ members S := by
  have h := memb_complete 16 0 S [] v (by simpa using hv) hb
  simpa [members] using h

theorem closeM_fold_mono : ∀ (L : List Nat) (acc h : Nat), mem acc h = true →
    mem (L.foldl (fun acc v => ins acc (cmpl v)) acc) h = true := by
  intro L; induction L with
  | nil => intro acc h hm; exact hm
  | cons v L ih => intro acc h hm; exact ih _ h (mem_ins_of_mem _ hm)

theorem closeM_fold_hit : ∀ (L : List Nat) (acc v : Nat), v ∈ L →
    mem (L.foldl (fun acc v => ins acc (cmpl v)) acc) (cmpl v) = true := by
  intro L; induction L with
  | nil => intro _ _ hv; exact absurd hv (by simp)
  | cons w L ih =>
    intro acc v hv
    rcases List.mem_cons.mp hv with h | h
    · subst h; exact closeM_fold_mono L _ _ (mem_ins_self _ _)
    · exact ih _ v h

theorem cmpl_lt (v : Nat) (hv : v < 65536) : cmpl v < 65536 := by
  have h := Nat.xor_lt_two_pow (n := 16) (by simpa using hv) (by decide : (65535:Nat) < 2 ^ 16)
  simpa [cmpl] using h

theorem nnot_mem_close (m v : Nat) (b : Bool) (hv : v < 65536) (hm : mem m v = true) :
    nnot b v ∈ members (closeM m) := by
  cases b
  · exact members_complete _ _ hv (closeM_fold_mono _ _ _ hm)
  · show v ^^^ cmask ∈ members (closeM m)
    have hin : v ∈ members m := members_complete _ _ hv hm
    exact members_complete _ _ (cmpl_lt v hv) (closeM_fold_hit _ _ _ hin)

def lv (k : Nat) : Nat × List Nat := (build2 k).getD k (0, [])

theorem build2_length : ∀ k, (build2 k).length = k + 1 := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => show ((build2 k) ++ [_]).length = k + 2; simp [ih]

theorem getD_build2 : ∀ k j, j ≤ k → (build2 k).getD j (0, []) = lv j := by
  intro k; induction k with
  | zero => intro j hj; have : j = 0 := by omega
            subst this; rfl
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · show ((build2 k) ++ [_]).getD j (0, []) = lv j
      rw [getD_append_left _ _ _ j (by rw [build2_length]; exact hlt)]
      exact ih j (by omega)
    · have : j = k + 1 := by omega
      subst this; rfl

theorem lv_succ (k : Nat) :
    lv (k + 1) = (stepM ((build2 k).map Prod.snd) k,
                  members (closeM (stepM ((build2 k).map Prod.snd) k))) := by
  show ((build2 k) ++ [_]).getD (k + 1) (0, []) = _
  have h := getD_append_right (build2 k)
    (stepM ((build2 k).map Prod.snd) k, members (closeM (stepM ((build2 k).map Prod.snd) k)))
    (0, [])
  rw [build2_length] at h; exact h

theorem lv_snd (k : Nat) : (lv k).2 = members (closeM (lv k).1) := by
  cases k with
  | zero => rfl
  | succ k => rw [lv_succ]

theorem getD_map_snd (l : List (Nat × List Nat)) (i : Nat) :
    (l.map Prod.snd).getD i [] = (l.getD i (0, [])).2 := by
  unfold List.getD; rw [List.getElem?_map]; cases l[i]? <;> rfl

def T (φ : Frm 4) : Nat := ttN (evalF φ)

theorem T_lt (φ : Frm 4) : T φ < 65536 := key_tab_lt _

theorem T_and (pa : Bool) (a : Frm 4) (pb : Bool) (b : Frm 4) :
    T (Frm.and pa a pb b) = gAnd pa (T a) pb (T b) := by
  refine eq_of_low _ _ (Low_ttN _) (Low_gAnd _ _ _ _ (Low_ttN _) (Low_ttN _)) (fun t ht => ?_)
  rw [T, testBit_ttN _ t ht, testBit_gAnd _ _ _ _ t ht, T, T, testBit_ttN _ t ht,
    testBit_ttN _ t ht]
  rfl

theorem T_var : ∀ i : Fin 4, mem L0M (T (Frm.var i)) = true := by decide
theorem T_one : mem L0M (T Frm.one) = true := by decide

theorem complete_k : ∀ φ : Frm 4, mem (lv (gatesF φ)).1 (T φ) = true := by
  intro φ
  induction φ with
  | var i => exact T_var i
  | one => exact T_one
  | and pa a pb b iha ihb =>
    have hg : gatesF (Frm.and pa a pb b) = (gatesF a + gatesF b) + 1 := by
      simp only [gatesF]; omega
    rw [hg, lv_succ, T_and]
    refine stepM_hit _ _ (gatesF a) _ _ (by omega) ?_ ?_
    · rw [getD_map_snd, getD_build2 _ _ (by omega), lv_snd]
      exact nnot_mem_close _ _ pa (T_lt a) iha
    · rw [getD_map_snd, show gatesF a + gatesF b - gatesF a = gatesF b by omega,
        getD_build2 _ _ (by omega), lv_snd]
      exact nnot_mem_close _ _ pb (T_lt b) ihb

theorem T_z : ttN z03de = zT := by decide
theorem T_nz : ttN (fun x => !(z03de x)) = cmpl zT := by decide

theorem land_absorb (a b : Nat) : a &&& (a &&& b) = a &&& b := by
  refine Nat.eq_of_testBit_eq (fun t => ?_)
  simp only [Nat.testBit_and]; cases a.testBit t <;> rfl

theorem no_small (φ : Frm 4) (hg : gatesF φ ≤ 6) (hz : T φ = zT ∨ T φ = cmpl zT) : False := by
  have hm := miss2_6
  simp only [miss2, miss2Of, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨hall, hhit⟩ := hm
  rcases Nat.lt_or_ge (gatesF φ) 6 with hlt | hge
  ·
    have hc := complete_k φ
    have hin : lv (gatesF φ) ∈ build2 5 := by
      rw [← getD_build2 5 (gatesF φ) (by omega)]
      unfold List.getD
      rw [List.getElem?_eq_getElem (by rw [build2_length]; omega)]
      exact List.getElem_mem _
    have hp := (List.all_eq_true.mp hall) _ hin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    rcases hz with h | h <;> rw [h] at hc <;> simp [hc] at hp
  ·
    have h6 : gatesF φ = 6 := by omega
    cases φ with
    | var i => simp [gatesF] at h6
    | one => simp [gatesF] at h6
    | and pa a pb b =>
      have hab : gatesF a + gatesF b = 5 := by simp only [gatesF] at h6; omega
      rw [T_and] at hz
      have ha : nnot pa (T a) ∈ ((build2 5).map Prod.snd).getD (gatesF a) [] := by
        rw [getD_map_snd, getD_build2 _ _ (by omega), lv_snd]
        exact nnot_mem_close _ _ pa (T_lt a) (complete_k a)
      have hb : nnot pb (T b) ∈ ((build2 5).map Prod.snd).getD (5 - gatesF a) [] := by
        rw [getD_map_snd, show 5 - gatesF a = gatesF b by omega,
          getD_build2 _ _ (by omega), lv_snd]
        exact nnot_mem_close _ _ pb (T_lt b) (complete_k b)
      have hh : hitNext ((build2 5).map Prod.snd) 5 zT = true := by
        simp only [hitNext, List.any_eq_true]
        refine ⟨gatesF a, List.mem_range.mpr (by omega), nnot pa (T a), ha, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
        unfold gAnd at hz
        refine ⟨?_, nnot pb (T b), hb, ?_⟩
        · rcases hz with h | h
          · left; rw [← h, land_absorb]
          · right; rw [← h, land_absorb]
        · exact hz
      rw [hh] at hhit; exact absurd hhit (by decide)

theorem tree_lower_k : ∀ k, HasFormula z03de k → 7 ≤ k := by
  intro k hk
  obtain ⟨φ, hle, hc⟩ := hk
  rcases Nat.lt_or_ge k 7 with hlt | hge
  · exfalso
    refine no_small φ (by omega) ?_
    rcases hc with h | h
    · left; rw [T, h, T_z]
    · right; rw [T, h, T_nz]
  · exact hge

theorem z03de_tree_k : IsTree z03de 7 := ⟨z03de_hasFormula7, tree_lower_k⟩

theorem has_emptyM (j : Nat) : has emptyM j = false := by
  unfold has emptyM
  rcases Nat.lt_or_ge j 65536 with h | h
  · rw [Array.getElem?_replicate]; simp [h]
  · rw [Array.getElem?_eq_none (by simpa using h)]; rfl

theorem has_add_inv {t : Marks} {v : List Bool} {j : Nat} (h : has (add t v) j = true) :
    has t j = true ∨ j = key v := by
  unfold has add at h
  rw [Array.set!, Array.getElem?_setIfInBounds] at h
  by_cases hij : key v = j
  · exact Or.inr hij.symm
  · rw [if_neg hij] at h; exact Or.inl h

def Good (k : Nat) (t : Marks) : Prop :=
  ∀ j, has t j = true → ∃ φ : Frm 4, gatesF φ = k ∧ key (tab (evalF φ)) = j

def GoodL (i : Nat) (A : List (List Bool)) : Prop :=
  ∀ a ∈ A, ∃ φ : Frm 4, gatesF φ = i ∧ tab (evalF φ) = a

theorem present_good {i : Nat} {t : Marks} (h : Good i t) : GoodL i (present t) := by
  intro a ha
  simp only [present, List.mem_filterMap, List.mem_range] at ha
  obtain ⟨j, _, hj⟩ := ha
  by_cases hh : has t j = true
  · rw [if_pos hh] at hj
    obtain ⟨φ, hg, hk⟩ := h j hh
    refine ⟨φ, hg, ?_⟩
    have hu := unkey_key (tab (evalF φ))
    rw [length_tab, hk] at hu
    rw [← hu]; exact Option.some.inj hj
  · rw [if_neg hh] at hj; exact absurd hj (by simp)

theorem addAll_good {k : Nat} : ∀ (l : List (List Bool)) (t : Marks), Good k t →
    (∀ w ∈ l, ∃ φ : Frm 4, gatesF φ = k ∧ tab (evalF φ) = w) → Good k (addAll t l) := by
  intro l; induction l with
  | nil => intro t ht _; exact ht
  | cons w l ih =>
    intro t ht hl
    refine ih (add t w) ?_ (fun w' hw' => hl w' (List.mem_cons_of_mem _ hw'))
    intro j hj
    rcases has_add_inv hj with h | h
    · exact ht j h
    · obtain ⟨φ, hg, hw⟩ := hl w (List.mem_cons_self ..)
      exact ⟨φ, hg, by rw [hw, h]⟩

theorem four_good {i j : Nat} {a b : List Bool}
    (ha : ∃ φ : Frm 4, gatesF φ = i ∧ tab (evalF φ) = a)
    (hb : ∃ φ : Frm 4, gatesF φ = j ∧ tab (evalF φ) = b) :
    ∀ w ∈ four a b, ∃ φ : Frm 4, gatesF φ = i + j + 1 ∧ tab (evalF φ) = w := by
  obtain ⟨φa, hga, rfl⟩ := ha
  obtain ⟨φb, hgb, rfl⟩ := hb
  intro w hw
  have hg : ∀ pa pb, gatesF (Frm.and pa φa pb φb) = i + j + 1 := by
    intro pa pb; simp only [gatesF]; omega
  simp only [four, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h | h <;> subst h
  · exact ⟨Frm.and false φa false φb, hg _ _, tab_and _ _ _ _⟩
  · exact ⟨Frm.and false φa true φb, hg _ _, tab_and _ _ _ _⟩
  · exact ⟨Frm.and true φa false φb, hg _ _, tab_and _ _ _ _⟩
  · exact ⟨Frm.and true φa true φb, hg _ _, tab_and _ _ _ _⟩

theorem combB_good {k i j : Nat} (a : List Bool)
    (ha : ∃ φ : Frm 4, gatesF φ = i ∧ tab (evalF φ) = a) (hk : k = i + j + 1) :
    ∀ (B : List (List Bool)) (t : Marks), GoodL j B → Good k t → Good k (combB a B t) := by
  intro B; induction B with
  | nil => intro t _ ht; exact ht
  | cons b B ih =>
    intro t hB ht
    refine ih _ (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')) ?_
    refine addAll_good _ _ ht ?_
    intro w hw
    obtain ⟨φ, hg, he⟩ := four_good ha (hB b (List.mem_cons_self ..)) w hw
    exact ⟨φ, by omega, he⟩

theorem combine_good {k i j : Nat} (hk : k = i + j + 1) :
    ∀ (A B : List (List Bool)) (t : Marks), GoodL i A → GoodL j B → Good k t →
      Good k (combine A B t) := by
  intro A; induction A with
  | nil => intro B t _ _ ht; exact ht
  | cons a A ih =>
    intro B t hA hB ht
    exact ih B _ (fun a' ha' => hA a' (List.mem_cons_of_mem _ ha')) hB
      (combB_good a (hA a (List.mem_cons_self ..)) hk B t hB ht)

theorem lvl_sound_le : ∀ n k, k ≤ n → Good k (lvl k) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    show Good 0 L0
    refine addAll_good leavesT emptyM (fun j h => by rw [has_emptyM] at h; exact absurd h (by simp)) ?_
    intro w hw
    simp only [leavesT, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h <;> subst h
    · exact ⟨Frm.var 0, rfl, rfl⟩
    · exact ⟨Frm.var 1, rfl, rfl⟩
    · exact ⟨Frm.var 2, rfl, rfl⟩
    · exact ⟨Frm.var 3, rfl, rfl⟩
    · exact ⟨Frm.one, rfl, rfl⟩
  | succ n ihn =>
    intro k' hk'
    have ih : ∀ i, i < k' → Good i (lvl i) := fun i hi => ihn i (by omega)
    cases k' with
    | zero =>
      show Good 0 L0
      refine addAll_good leavesT emptyM (fun j h => by rw [has_emptyM] at h; exact absurd h (by simp)) ?_
      intro w hw
      simp only [leavesT, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h <;> subst h
      · exact ⟨Frm.var 0, rfl, rfl⟩
      · exact ⟨Frm.var 1, rfl, rfl⟩
      · exact ⟨Frm.var 2, rfl, rfl⟩
      · exact ⟨Frm.var 3, rfl, rfl⟩
      · exact ⟨Frm.one, rfl, rfl⟩
    | succ k =>
      rw [lvl_succ_eq, stepL]
      have hfold : ∀ (L : List Nat) (t : Marks), (∀ i ∈ L, i ≤ k) → Good (k + 1) t →
          Good (k + 1) (L.foldl (stepF (levels k) k) t) := by
        intro L; induction L with
        | nil => intro t _ ht; exact ht
        | cons i L ihL =>
          intro t hL ht
          have hi : i ≤ k := hL i (List.mem_cons_self ..)
          refine ihL _ (fun i' hi' => hL i' (List.mem_cons_of_mem _ hi')) ?_
          unfold stepF
          rw [getD_levels k i hi, getD_levels k (k - i) (by omega)]
          exact combine_good (i := i) (j := k - i) (by omega) _ _ t
            (present_good (ih i (by omega))) (present_good (ih (k - i) (by omega))) ht
      exact hfold _ emptyM (fun i hi => by simp at hi; omega)
        (fun j h => by rw [has_emptyM] at h; exact absurd h (by simp))

theorem lvl_sound (k : Nat) : Good k (lvl k) := lvl_sound_le k k (Nat.le_refl k)

theorem key_tab_inj {f g : Func 4} (h : key (tab f) = key (tab g)) : f = g := by
  have hf := unkey_key (tab f)
  have hg := unkey_key (tab g)
  rw [length_tab] at hf hg
  have ht : tab f = tab g := by rw [← hf, ← hg, h]
  refine funext16 (fun t hlt => ?_)
  have h1 : (tab f)[t]? = (tab g)[t]? := by rw [ht]
  simp only [tab, List.getElem?_map, List.getElem?_range hlt] at h1
  exact Option.some.inj h1

theorem dp_miss_k : (List.range 7).all (fun j =>
    (!has (lvl j) (key (tab z03de))) && (!has (lvl j) (key (tab (fun x => !(z03de x)))))) = true := by
  refine List.all_eq_true.mpr (fun j hj => ?_)
  have hj7 : j < 7 := List.mem_range.mp hj
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · cases h : has (lvl j) (key (tab z03de))
    · rfl
    · obtain ⟨φ, hg, hk⟩ := lvl_sound j _ h
      exact (no_small φ (by omega) (Or.inl (by rw [T, ttN, key_tab_inj hk, ← ttN, T_z]))).elim
  · cases h : has (lvl j) (key (tab (fun x => !(z03de x))))
    · rfl
    · obtain ⟨φ, hg, hk⟩ := lvl_sound j _ h
      exact (no_small φ (by omega) (Or.inr (by rw [T, ttN, key_tab_inj hk, ← ttN, T_nz]))).elim

end DP4K

theorem dp_miss : (List.range 7).all (fun j =>
    (!has (lvl j) (key (tab z03de))) && (!has (lvl j) (key (tab (fun x => !(z03de x)))))) = true :=
  DP4K.dp_miss_k

theorem tree_lower : ∀ k, HasFormula z03de k → 7 ≤ k := by
  intro k hk
  obtain ⟨φ, hle, hc⟩ := hk
  rcases Nat.lt_or_ge k 7 with hlt | hge
  · exfalso
    have hmem : gatesF φ ∈ List.range 7 := List.mem_range.mpr (by omega)
    have hall := (List.all_eq_true.mp dp_miss) (gatesF φ) hmem
    have hd := dp_complete φ
    rcases hc with h1 | h1 <;> rw [h1] at hd <;> simp [hd] at hall
  · exact hge

theorem z03de_tree : IsTree z03de 7 := ⟨z03de_hasFormula7, tree_lower⟩

#print axioms dp_miss
#print axioms z03de_tree

theorem tt_out (gs : List Gate) (hwf : wfC 4 gs) (hne : gs ≠ []) (f : Func 4)
    (hc : CircuitComputes gs f) :
    (ttsOf gs).getD (gs.length - 1) 0 = ttN f
      ∨ (ttsOf gs).getD (gs.length - 1) 0 = nnot true (ttN f) := by
  have hlast : gs.length - 1 < gs.length := by
    cases gs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  rcases hc with h | h
  · refine Or.inl (eq_of_low _ _ (low_ttsOf gs _) (Low_ttN f) (fun t ht => ?_))
    rw [testBit_ttsOf t ht gs hwf _ hlast, testBit_ttN f t ht]
    exact h (asg t)
  · refine Or.inr (eq_of_low _ _ (low_ttsOf gs _) (Low_nnot true _ (Low_ttN f)) (fun t ht => ?_))
    rw [testBit_ttsOf t ht gs hwf _ hlast, testBit_nnot true _ t ht, testBit_ttN f t ht]
    have hh := h (asg t)
    unfold circuitOut at hh
    rw [hh]
    cases f (asg t) <;> rfl

theorem normFrom_of_opt (f : Func 4) (gs : List Gate) (m : Nat)
    (h0 : f ≠ fun _ => false) (h1 : f ≠ fun _ => true)
    (hwf : wfC 4 gs) (hopt : IsOpt f m) (hlen : gs.length = m) (hc : CircuitComputes gs f)
    (hle : ∀ g ∈ gs, g.ia ≤ g.ib) :
    ∀ (suf pre : List Gate), pre ++ suf = gs → NormFrom pre suf := by
  intro suf
  induction suf with
  | nil => intro _ _; exact True.intro
  | cons g rest ih =>
    intro pre hcat
    have hgmem : g ∈ gs := by
      rw [← hcat]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    cases rest with
    | nil => exact hle g hgmem
    | cons g2 r2 =>
      refine ⟨hle g hgmem, ?_, ?_⟩
      · exact redundant_false f gs m h0 h1 hwf hopt hlen hc pre g (g2 :: r2) hcat.symm (by simp)
      · exact ih (pre ++ [g]) (by simpa using hcat)

theorem hasCircuit_mono (f : Func 4) (a b : Nat) (h : a ≤ b) (hc : HasCircuit f a) :
    HasCircuit f b := by
  obtain ⟨gs, hwf, hlen, hcc⟩ := hc
  exact ⟨gs, hwf, by omega, hcc⟩

theorem exists_min (P : Nat → Prop) (mono : ∀ a b, a ≤ b → P a → P b) :
    ∀ N, P N → ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  intro N
  induction N with
  | zero => intro h; exact ⟨0, h, fun k _ => Nat.zero_le k⟩
  | succ N ih =>
    intro h
    rcases Classical.em (P N) with hN | hN
    · exact ih hN
    · refine ⟨N + 1, h, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k (N + 1) with hlt | hge
      · exact absurd (mono k N (by omega) hk) hN
      · exact hge

def z6gs : List Gate :=
  [⟨false, 0, true, 1⟩, ⟨true, 1, true, 2⟩, ⟨true, 3, true, 4⟩,
   ⟨false, 5, false, 6⟩, ⟨true, 5, true, 6⟩, ⟨true, 7, true, 8⟩]

theorem z6_wf : wfC 4 z6gs := by
  intro q
  obtain ⟨i, hi⟩ := q
  simp only [z6gs, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by decide +revert, by decide +revert⟩
  | 1, _ => exact ⟨by decide +revert, by decide +revert⟩
  | 2, _ => exact ⟨by decide +revert, by decide +revert⟩
  | 3, _ => exact ⟨by decide +revert, by decide +revert⟩
  | 4, _ => exact ⟨by decide +revert, by decide +revert⟩
  | 5, _ => exact ⟨by decide +revert, by decide +revert⟩
  | (k + 6), h => exact absurd h (by omega)

theorem z6_computes : CircuitComputes z6gs z03de := by
  have h : (fun x => circuitOut x z6gs) = z03de := funext16' (by decide)
  exact Or.inl (fun x => congrFun h x)

theorem z03de_hasCircuit6 : HasCircuit z03de 6 := ⟨z6gs, z6_wf, by decide, z6_computes⟩

theorem z03de_ne_false : z03de ≠ fun _ => false := by
  intro h
  have h1 : z03de (asg 1) = false := congrFun h (asg 1)
  have h2 : z03de (asg 1) = true := by decide
  rw [h1] at h2
  exact absurd h2 (by simp)

theorem z03de_ne_true : z03de ≠ fun _ => true := by
  intro h
  have h1 : z03de (asg 0) = true := congrFun h (asg 0)
  have h2 : z03de (asg 0) = false := by decide
  rw [h1] at h2
  exact absurd h2 (by simp)

theorem anyC_miss : (List.range 5).all (fun k => !anyC (k + 1) [] (ttN z03de)) = true := by
  native_decide

theorem opt_ge_6 : ∀ m, IsOpt z03de m → 6 ≤ m := by
  intro m hopt
  rcases Nat.lt_or_ge m 6 with hlt | hge
  · exfalso
    obtain ⟨gs0, hwf0, hlen0, hc0⟩ := hopt.1
    have hlen : gs0.length = m :=
      Nat.le_antisymm hlen0 (hopt.2 _ ⟨gs0, hwf0, Nat.le_refl _, hc0⟩)
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · exfalso
        have hnil : gs0 = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        rcases empty_only_const 4 z03de hc0 with hcf | hcf
        · exact z03de_ne_false (funext hcf)
        · exact z03de_ne_true (funext hcf)
      · exact h
    have hwf : wfC 4 (normC gs0) := wfC_normC gs0 hwf0
    have hlenN : (normC gs0).length = m := by rw [length_normC]; exact hlen
    have hc : CircuitComputes (normC gs0) z03de := circuitComputes_normC gs0 z03de hc0
    have hne : normC gs0 ≠ [] := by
      intro h
      rw [h] at hlenN
      simp at hlenN
      omega
    have hnorm : NormFrom [] (normC gs0) :=
      normFrom_of_opt z03de (normC gs0) m z03de_ne_false z03de_ne_true hwf hopt hlenN hc
        (mem_normC_le gs0) (normC gs0) [] (by simp)
    have hval := tt_out (normC gs0) hwf hne z03de hc
    have hany : anyC (normC gs0).length (ttsOf []) (ttN z03de) = true :=
      anyC_of_norm (normC gs0) [] (ttN z03de) (by simpa using hwf) hne hnorm (by simpa using hval)
    rw [hlenN] at hany
    have h0 : ttsOf [] = [] := rfl
    rw [h0] at hany
    have hk : m - 1 ∈ List.range 5 := List.mem_range.mpr (by omega)
    have hmiss := (List.all_eq_true.mp anyC_miss) (m - 1) hk
    have hm : m - 1 + 1 = m := by omega
    rw [hm, hany] at hmiss
    simp at hmiss
  · exact hge

theorem z03de_isOpt6 : IsOpt z03de 6 := by
  obtain ⟨m, hm⟩ := exists_min (HasCircuit z03de)
    (fun a b h hc => hasCircuit_mono z03de a b h hc) 6 z03de_hasCircuit6
  have h6 : 6 ≤ m := opt_ge_6 m hm
  have hm6 : m ≤ 6 := hm.2 6 z03de_hasCircuit6
  have hme : m = 6 := by omega
  subst hme
  exact hm

theorem z03de_gap1 : Gap z03de 1 := ⟨6, 7, z03de_isOpt6, z03de_tree, by omega⟩

theorem z03de_essential : ∀ i : Fin 4, dependsOn z03de i := by
  intro i
  refine ⟨asg 0, ?_⟩
  match i with
  | ⟨0, _⟩ => decide +revert
  | ⟨1, _⟩ => decide +revert
  | ⟨2, _⟩ => decide +revert
  | ⟨3, _⟩ => decide +revert
  | ⟨k + 4, h⟩ => exact absurd h (by omega)

#print axioms dp_complete
#print axioms testBit_ttsOf
#print axioms anyC_of_norm
#print axioms redundant_false
#print axioms z6_computes
#print axioms phi7_computes
#print axioms z03de_essential
#print axioms z03de_isOpt6
#print axioms z03de_gap1

end Witness4
