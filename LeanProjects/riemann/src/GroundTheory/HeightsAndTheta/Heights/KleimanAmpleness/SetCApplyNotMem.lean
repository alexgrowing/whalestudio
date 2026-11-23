import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellPosExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellContract

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

def rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : ∀ k, Finset (ι k) :=
  Function.update I p.1 ((I p.1).erase p.2)

omit [Fintype K] in
theorem rem_apply_of_ne {I : ∀ k, Finset (ι k)} {k l : K} (i : ι k) (h : l ≠ k) :
    rem I ⟨k, i⟩ l = I l :=
  Function.update_of_ne h _ _

omit [Fintype K] in
theorem rem_apply_self (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) :
    rem I ⟨k, i⟩ k = (I k).erase i :=
  Function.update_self _ _ _

omit [Fintype K] in
theorem rem_apply_subset (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) (l : K) : rem I p l ⊆ I l := by
  obtain ⟨k, i⟩ := p
  by_cases hl : l = k
  · subst hl; rw [rem_apply_self]; exact Finset.erase_subset _ _
  · rw [rem_apply_of_ne i hl]

omit [∀ k, LinearOrder (ι k)] in

theorem offset_update (I : ∀ k, Finset (ι k)) (k : K) (X : Finset (ι k)) :
    ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k X l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
  Finset.sum_congr rfl fun l hl => by
    rw [Function.update_of_ne (ne_of_lt (Finset.mem_filter.1 hl).2)]

theorem sign_swap_same {I : ∀ k, Finset (ι k)} {k : K} {i i' : ι k} (hi : i ∈ I k) (hlt : i < i') :
    faceSign I k i' * faceSign (rem I ⟨k, i'⟩) k i = -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k i') := by
  have h1 : ((I k).erase i').filter (· < i) = (I k).filter (· < i) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzi⟩; exact ⟨hz, hzi⟩
    · rintro ⟨hz, hzi⟩; exact ⟨⟨(hzi.trans hlt).ne, hz⟩, hzi⟩
  have h3 : i ∈ (I k).filter (· < i') := Finset.mem_filter.2 ⟨hi, hlt⟩
  have h2 : (((I k).erase i).filter (· < i')).card + 1 = ((I k).filter (· < i')).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold faceSign rem
  simp only [Function.update_self, offset_update]
  rw [h1, ← h2]
  ring

theorem sign_swap_lt {I : ∀ k, Finset (ι k)} {k k' : K} (i : ι k) (i' : ι k') (hi : i ∈ I k)
    (hk : k < k') (h2 : 2 ≤ (I k).card) :
    faceSign I k' i' * faceSign (rem I ⟨k', i'⟩) k i =
      -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k' i') := by
  have hmem : k ∈ Finset.univ.filter (· < k') := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  have hoff : ∑ l ∈ Finset.univ.filter (· < k'), ((Function.update I k ((I k).erase i) l).card - 1) + 1 =
      ∑ l ∈ Finset.univ.filter (· < k'), ((I l).card - 1) := by
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, Function.update_self,
      Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)],
      Finset.card_erase_of_mem hi]
    omega
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k' ((I k').erase i') l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by
      rw [Function.update_of_ne (ne_of_lt ((Finset.mem_filter.1 hl).2.trans hk))]
  unfold faceSign rem
  simp only [Function.update_of_ne hk.ne, Function.update_of_ne hk.ne', hlow]
  rw [← hoff]
  ring

omit [Fintype K] [LinearOrder K] in
theorem two_le_card {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k)
    (h : ((I k).erase i).Nonempty) : 2 ≤ (I k).card := by
  have := h.card_pos
  rw [Finset.card_erase_of_mem hi] at this
  omega

theorem sign_swap {I : ∀ k, Finset (ι k)} {p q : Σ k, ι k} (hp : p.2 ∈ I p.1) (hq : q.2 ∈ I q.1)
    (hne : q ≠ p) (hJ : ∀ l, (rem (rem I p) q l).Nonempty) :
    faceSign I p.1 p.2 * faceSign (rem I p) q.1 q.2 =
      -(faceSign I q.1 q.2 * faceSign (rem I q) p.1 p.2) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  rcases lt_trichotomy k k' with h | rfl | h
  · have hb := hJ k
    rw [rem_apply_of_ne _ h.ne, rem_apply_self] at hb
    rw [sign_swap_lt i i' hp h (two_le_card hp hb), neg_neg]
  · have hii : i' ≠ i := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hii with h | h
    · exact sign_swap_same hq h
    · rw [sign_swap_same hp h, neg_neg]
  · have hb := hJ k'
    rw [rem_apply_self, rem_apply_of_ne _ h.ne] at hb
    exact sign_swap_lt i' i hq h (two_le_card hq hb)

theorem faceSign_mul_self (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) :
    faceSign I k i * faceSign I k i = 1 := by
  unfold faceSign
  rw [← mul_pow]
  norm_num

theorem neg_one_pow_pair (x y z : ℕ) (h : x + y = 1) :
    ((-1 : ℤ) ^ (x + z)) * (-1) ^ (y + z) = -1 := by
  rw [← pow_add, show x + z + (y + z) = 2 * z + 1 by omega, pow_succ, pow_mul]
  norm_num

theorem faceSign_pair {I : ∀ k, Finset (ι k)} {k : K} {a b : ι k} (h : I k = {a, b}) (hab : a ≠ b) :
    faceSign I k a * faceSign I k b = -1 := by
  have hc : ((I k).filter (· < a)).card + ((I k).filter (· < b)).card = 1 := by
    rw [h]
    rcases lt_or_gt_of_ne hab with h' | h'
    · simp [Finset.filter_insert, Finset.filter_singleton, h', not_lt.2 h'.le]
    · simp [Finset.filter_insert, Finset.filter_singleton, h', not_lt.2 h'.le]
  exact neg_one_pow_pair _ _ _ hc

theorem faceSign_congr {I I' : ∀ k, Finset (ι k)} {l : K} (i : ι l) (hl : I l = I' l)
    (hc : ∀ m, (I m).card = (I' m).card) : faceSign I l i = faceSign I' l i := by
  unfold faceSign
  rw [hl]
  simp only [hc]

def addC (c : ∀ k, ι k) (I : ∀ k, Finset (ι k)) (k : K) : ∀ k, Finset (ι k) :=
  Function.update I k (insert (c k) (I k))

def setC (c : ∀ k, ι k) (T : Finset K) (I : ∀ k, Finset (ι k)) : ∀ k, Finset (ι k) :=
  fun j => if j ∈ T then {c j} else I j

omit [Fintype K] in
theorem addC_apply_self (c : ∀ k, ι k) (I : ∀ k, Finset (ι k)) (k : K) : addC c I k k = insert (c k) (I k) :=
  Function.update_self _ _ _

omit [Fintype K] in
theorem addC_apply_of_ne (c : ∀ k, ι k) (I : ∀ k, Finset (ι k)) {k l : K} (h : l ≠ k) : addC c I k l = I l :=
  Function.update_of_ne h _ _

omit [Fintype K] in
theorem subset_addC (c : ∀ k, ι k) (I : ∀ k, Finset (ι k)) (k l : K) : I l ⊆ addC c I k l := by
  by_cases hl : l = k
  · subst hl; rw [addC_apply_self]; exact Finset.subset_insert _ _
  · rw [addC_apply_of_ne c I hl]

omit [Fintype K] in
theorem rem_addC {c : ∀ k, ι k} {I : ∀ k, Finset (ι k)} {k : K} (h : c k ∉ I k) :
    rem (addC c I k) ⟨k, c k⟩ = I := by
  unfold rem addC
  simp only [Function.update_idem, Function.update_self, Finset.erase_insert h, Function.update_eq_self]

omit [Fintype K] in
theorem addC_rem {c : ∀ k, ι k} {I : ∀ k, Finset (ι k)} {k : K} (h : c k ∈ I k) :
    addC c (rem I ⟨k, c k⟩) k = I := by
  unfold rem addC
  simp only [Function.update_idem, Function.update_self, Finset.insert_erase h, Function.update_eq_self]

omit [Fintype K] in
theorem rem_addC_comm {c : ∀ k, ι k} {I : ∀ k, Finset (ι k)} {k l : K} {i : ι l} (hi : i ∈ I l)
    (h : c k ∉ I k) : rem (addC c I k) ⟨l, i⟩ = addC c (rem I ⟨l, i⟩) k := by
  by_cases hl : l = k
  · subst hl
    have hne : c l ≠ i := fun e => h (e ▸ hi)
    unfold rem addC
    simp only [Function.update_idem, Function.update_self]
    rw [Finset.erase_insert_of_ne hne]
  · unfold rem addC
    simp only [Function.update_of_ne hl]
    rw [Function.update_comm (Ne.symm hl)]
    simp only [Function.update_of_ne (Ne.symm hl)]

omit [Fintype K] [∀ k, LinearOrder (ι k)] in
theorem setC_apply_mem {c : ∀ k, ι k} {T : Finset K} {I : ∀ k, Finset (ι k)} {j : K} (h : j ∈ T) :
    setC c T I j = {c j} :=
  if_pos h

omit [Fintype K] [∀ k, LinearOrder (ι k)] in
theorem setC_apply_not_mem {c : ∀ k, ι k} {T : Finset K} {I : ∀ k, Finset (ι k)} {j : K} (h : j ∉ T) :
    setC c T I j = I j :=
  if_neg h

omit [Fintype K] in
theorem rem_setC {c : ∀ k, ι k} {T : Finset K} {I : ∀ k, Finset (ι k)} {l : K} (i : ι l) (hl : l ∉ T) :
    setC c T (rem I ⟨l, i⟩) = rem (setC c T I) ⟨l, i⟩ := by
  funext j
  by_cases hj : j ∈ T
  · have : j ≠ l := fun e => hl (e ▸ hj)
    rw [setC_apply_mem hj, rem_apply_of_ne i this, setC_apply_mem hj]
  · rw [setC_apply_not_mem hj]
    by_cases hjl : j = l
    · subst hjl; rw [rem_apply_self, rem_apply_self, setC_apply_not_mem hj]
    · rw [rem_apply_of_ne i hjl, rem_apply_of_ne i hjl, setC_apply_not_mem hj]

omit [Fintype K] [∀ k, LinearOrder (ι k)] in
theorem setC_setC {c : ∀ k, ι k} {T : Finset K} {I : ∀ k, Finset (ι k)} {k : K} (hk : k ∉ T) :
    setC c {k} (setC c T I) = setC c (insert k T) I := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [setC_apply_mem (Finset.mem_singleton_self _), setC_apply_mem (Finset.mem_insert_self _ _)]
  · rw [setC_apply_not_mem (by simpa using hj)]
    by_cases hjT : j ∈ T
    · rw [setC_apply_mem hjT, setC_apply_mem (Finset.mem_insert_of_mem hjT)]
    · rw [setC_apply_not_mem hjT, setC_apply_not_mem (by simp [hj, hjT])]

theorem sum_addC {M : Type} [AddCommMonoid M] (c : ∀ k, ι k) (I : ∀ k, Finset (ι k)) (k : K) (hck : c k ∉ I k)
    (F : (l : K) → ι l → M) :
    ∑ l, ∑ i ∈ addC c I k l, F l i = F k (c k) + ∑ l, ∑ i ∈ I l, F l i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    addC_apply_self, Finset.sum_insert hck, add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun l hl => by rw [addC_apply_of_ne c I (Finset.ne_of_mem_erase hl)]

omit [Fintype K] in

theorem telescope {M : Type} [AddCommGroup M] (g : Finset K → M) (s : Finset K) :
    ∑ k ∈ s, (g (s.filter (· < k)) - g (s.filter (· ≤ k))) = g ∅ - g s := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have e1 : (insert a s).filter (· < a) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have e2 : (insert a s).filter (· ≤ a) = insert a s :=
      Finset.filter_true_of_mem fun x hx => by
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact le_rfl
        · exact (ha x hx).le
    have e3 : ∀ k ∈ s, (insert a s).filter (· < k) = s.filter (· < k) ∧
        (insert a s).filter (· ≤ k) = s.filter (· ≤ k) := by
      intro k hk
      have hak : ¬ a < k := not_lt.2 (ha k hk).le
      have hak' : ¬ a ≤ k := not_le.2 (ha k hk)
      exact ⟨by rw [Finset.filter_insert, if_neg hak], by rw [Finset.filter_insert, if_neg hak']⟩
    rw [Finset.sum_insert has, e1, e2, Finset.sum_congr rfl fun k hk => by rw [(e3 k hk).1, (e3 k hk).2], ih]
    abel

variable {Ω : Type} [Field Ω]

def Good (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  (∀ k, (I k).Nonempty) ∧ CellMeets y I

def Supp (y : (Σ k, ι k) → Ω) (f : (∀ k, Finset (ι k)) → Ω) : Prop :=
  ∀ I, ¬ Good y I → f I = 0

open Classical in

def dif (y : (Σ k, ι k) → Ω) (f : (∀ k, Finset (ι k)) → Ω) (I : ∀ k, Finset (ι k)) : Ω :=
  if Good y I then ∑ k, ∑ i ∈ I k, faceSign I k i • f (rem I ⟨k, i⟩) else 0

open Classical in

def coneOp (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) (f : (∀ k, Finset (ι k)) → Ω)
    (I : ∀ k, Finset (ι k)) : Ω :=
  if Good y I ∧ c k ∉ I k then faceSign (addC c I k) k (c k) • f (addC c I k) else 0

open Classical in

def projOp (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (T : Finset K) (f : (∀ k, Finset (ι k)) → Ω)
    (I : ∀ k, Finset (ι k)) : Ω :=
  if Good y I ∧ ∀ j ∈ T, (I j).card = 1 then f (setC c T I) else 0

variable {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}

theorem dif_of_good {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)} (h : Good y I) :
    dif y f I = ∑ k, ∑ i ∈ I k, faceSign I k i • f (rem I ⟨k, i⟩) := by
  rw [dif, if_pos h]

theorem dif_of_not {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)} (h : ¬ Good y I) :
    dif y f I = 0 := by
  rw [dif, if_neg h]

theorem coneOp_of_good {k : K} {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)} (h : Good y I)
    (hk : c k ∉ I k) : coneOp y c k f I = faceSign (addC c I k) k (c k) • f (addC c I k) := by
  rw [coneOp, if_pos ⟨h, hk⟩]

theorem coneOp_of_not {k : K} {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)}
    (h : ¬ (Good y I ∧ c k ∉ I k)) : coneOp y c k f I = 0 := by
  rw [coneOp, if_neg h]

omit [∀ k, LinearOrder (ι k)] in
theorem projOp_of_good {T : Finset K} {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)} (h : Good y I)
    (hT : ∀ j ∈ T, (I j).card = 1) : projOp y c T f I = f (setC c T I) := by
  rw [projOp, if_pos ⟨h, hT⟩]

omit [∀ k, LinearOrder (ι k)] in
theorem projOp_of_not {T : Finset K} {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)}
    (h : ¬ (Good y I ∧ ∀ j ∈ T, (I j).card = 1)) : projOp y c T f I = 0 := by
  rw [projOp, if_neg h]

omit [Fintype K] in
theorem meets_rem {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (p : Σ k, ι k) : CellMeets y (rem I p) :=
  fun l j hj => hI l j (rem_apply_subset I p l hj)

omit [Fintype K] in
theorem good_rem {I : ∀ k, Finset (ι k)} (hI : Good y I) {k : K} {i : ι k} (h : ((I k).erase i).Nonempty) :
    Good y (rem I ⟨k, i⟩) := by
  refine ⟨fun l => ?_, meets_rem hI.2 _⟩
  by_cases hl : l = k
  · subst hl; rw [rem_apply_self]; exact h
  · rw [rem_apply_of_ne i hl]; exact hI.1 l

omit [Fintype K] in
theorem good_addC (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : Good y I) (k : K) :
    Good y (addC c I k) := by
  refine ⟨fun l => ?_, fun l j hj => ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [addC_apply_self]; exact Finset.insert_nonempty _ _
    · rw [addC_apply_of_ne c I hl]; exact hI.1 l
  · by_cases hl : l = k
    · subst hl
      rw [addC_apply_self, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hc l
      · exact hI.2 l j hj
    · rw [addC_apply_of_ne c I hl] at hj; exact hI.2 l j hj

omit [Fintype K] [∀ k, LinearOrder (ι k)] in
theorem good_setC (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : Good y I) (T : Finset K) :
    Good y (setC c T I) := by
  refine ⟨fun l => ?_, fun l j hj => ?_⟩
  · by_cases hl : l ∈ T
    · rw [setC_apply_mem hl]; exact Finset.singleton_nonempty _
    · rw [setC_apply_not_mem hl]; exact hI.1 l
  · by_cases hl : l ∈ T
    · rw [setC_apply_mem hl, Finset.mem_singleton] at hj; subst hj; exact hc l
    · rw [setC_apply_not_mem hl] at hj; exact hI.2 l j hj

theorem supp_coneOp (k : K) (f : (∀ k, Finset (ι k)) → Ω) : Supp y (coneOp y c k f) :=
  fun _ h => coneOp_of_not fun h' => h h'.1

theorem dif_coneOp (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : (∀ k, Finset (ι k)) → Ω} (hf : Supp y f) (k : K)
    (I : ∀ k, Finset (ι k)) :
    dif y (coneOp y c k f) I + coneOp y c k (dif y f) I = f I - projOp y c {k} f I := by
  by_cases hI : Good y I
  swap
  · rw [dif_of_not hI, coneOp_of_not (fun h => hI h.1), projOp_of_not (fun h => hI h.1), hf I hI]
    simp
  by_cases hck : c k ∈ I k
  · rw [coneOp_of_not (fun h => h.2 hck), add_zero, dif_of_good hI]
    rw [Finset.sum_eq_single k]
    rotate_left
    · intro l _ hl
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [coneOp_of_not, smul_zero]
      rintro ⟨-, h⟩
      exact h (by rw [rem_apply_of_ne i (Ne.symm hl)]; exact hck)
    · intro h; exact absurd (Finset.mem_univ k) h
    rw [Finset.sum_eq_single (c k)]
    rotate_left
    · intro i _ hne
      rw [coneOp_of_not, smul_zero]
      rintro ⟨-, h⟩
      exact h (by rw [rem_apply_self]; exact Finset.mem_erase.2 ⟨Ne.symm hne, hck⟩)
    · intro h; exact absurd hck h
    by_cases hne : ((I k).erase (c k)).Nonempty
    · have hnin : c k ∉ rem I ⟨k, c k⟩ k := by rw [rem_apply_self]; exact Finset.notMem_erase _ _
      rw [coneOp_of_good (good_rem hI hne) hnin, addC_rem hck, smul_smul, faceSign_mul_self, one_smul]
      have hP : projOp y c {k} f I = 0 := projOp_of_not fun h => by
        have h1 := two_le_card hck hne
        have h2 := h.2 k (Finset.mem_singleton_self k)
        omega
      rw [hP, sub_zero]
    · have hg : ¬ Good y (rem I ⟨k, c k⟩) := fun h => hne (by simpa [rem_apply_self] using h.1 k)
      rw [coneOp_of_not (fun h => hg h.1), smul_zero]
      have hempty : (I k).erase (c k) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
      have hIk : I k = {c k} := Finset.eq_singleton_iff_unique_mem.2 ⟨hck, fun x hx => by
        by_contra h
        have : x ∈ (I k).erase (c k) := Finset.mem_erase.2 ⟨h, hx⟩
        rw [hempty] at this
        exact Finset.notMem_empty _ this⟩
      have hset : setC c {k} I = I := by
        funext j
        by_cases hj : j = k
        · subst hj; rw [setC_apply_mem (Finset.mem_singleton_self _), hIk]
        · rw [setC_apply_not_mem (by simpa using hj)]
      rw [projOp_of_good hI (by simp [hIk]), hset, sub_self]
  · have hJ := good_addC hc hI k
    have key : ∀ l, ∀ i ∈ I l, faceSign I l i • coneOp y c k f (rem I ⟨l, i⟩) +
        faceSign (addC c I k) k (c k) • faceSign (addC c I k) l i • f (rem (addC c I k) ⟨l, i⟩) =
        if (I l).erase i = ∅ ∧ l = k then -f (setC c {k} I) else 0 := by
      intro l i hi
      by_cases hne : ((I l).erase i).Nonempty
      · have hg := good_rem hI hne
        have hnin : c k ∉ rem I ⟨l, i⟩ k := fun h => hck (rem_apply_subset I _ k h)
        have hne' : (⟨l, i⟩ : Σ k, ι k) ≠ ⟨k, c k⟩ := by
          intro h
          obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
          exact hck (by rw [← eq_of_heq h2]; exact hi)
        have e1 := sign_swap (I := addC c I k) (p := ⟨k, c k⟩) (q := ⟨l, i⟩)
          (show c k ∈ addC c I k k by rw [addC_apply_self]; exact Finset.mem_insert_self _ _)
          (show i ∈ addC c I k l from subset_addC c I k l hi) hne'
          (by rw [rem_addC hck]; exact hg.1)
        dsimp only at e1
        rw [rem_addC hck] at e1
        rw [coneOp_of_good hg hnin, ← rem_addC_comm hi hck, smul_smul, smul_smul, ← add_smul,
          if_neg (fun h => hne.ne_empty h.1)]
        have hε := faceSign_mul_self (addC c I k) k (c k)
        have hσ := faceSign_mul_self (rem (addC c I k) ⟨l, i⟩) k (c k)
        have hsum : faceSign I l i * faceSign (rem (addC c I k) ⟨l, i⟩) k (c k) +
            faceSign (addC c I k) k (c k) * faceSign (addC c I k) l i = 0 := by
          linear_combination (faceSign (addC c I k) k (c k) * faceSign (rem (addC c I k) ⟨l, i⟩) k (c k)) * e1 -
            (faceSign I l i * faceSign (rem (addC c I k) ⟨l, i⟩) k (c k)) * hε -
            (faceSign (addC c I k) k (c k) * faceSign (addC c I k) l i) * hσ
        rw [hsum, zero_smul]
      · have hempty : (I l).erase i = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
        have hg : ¬ Good y (rem I ⟨l, i⟩) := fun h => hne (by simpa [rem_apply_self] using h.1 l)
        rw [coneOp_of_not (fun h => hg h.1), smul_zero, zero_add]
        by_cases hlk : l = k
        · subst hlk
          rw [if_pos ⟨hempty, rfl⟩]
          have hIl : I l = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun x hx => by
            by_contra h
            have : x ∈ (I l).erase i := Finset.mem_erase.2 ⟨h, hx⟩
            rw [hempty] at this
            exact Finset.notMem_empty _ this⟩
          have hci : c l ≠ i := fun e => hck (by rw [e]; exact hi)
          have hset : rem (addC c I l) ⟨l, i⟩ = setC c {l} I := by
            funext j
            by_cases hj : j = l
            · subst hj
              rw [rem_apply_self, addC_apply_self, setC_apply_mem (Finset.mem_singleton_self _),
                Finset.erase_insert_of_ne hci, hempty]
              simp
            · rw [rem_apply_of_ne i hj, addC_apply_of_ne c I hj, setC_apply_not_mem (by simpa using hj)]
          have hpair : faceSign (addC c I l) l (c l) * faceSign (addC c I l) l i = -1 :=
            faceSign_pair (by rw [addC_apply_self, hIl]) hci
          rw [hset, smul_smul, hpair, neg_one_smul]
        · rw [if_neg (fun h => hlk h.2)]
          have hbad : ¬ Good y (rem (addC c I k) ⟨l, i⟩) := fun h => hne (by
            have := h.1 l
            rwa [rem_apply_self, addC_apply_of_ne c I hlk] at this)
          rw [hf _ hbad, smul_zero, smul_zero]
    have hsum : ∑ l, ∑ i ∈ I l, (if (I l).erase i = ∅ ∧ l = k then -f (setC c {k} I) else 0) =
        -projOp y c {k} f I := by
      rw [Finset.sum_eq_single k (fun l _ hl => Finset.sum_eq_zero fun i _ => if_neg fun h => hl h.2)
        (fun h => absurd (Finset.mem_univ k) h)]
      by_cases h1 : (I k).card = 1
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
        rw [projOp_of_good hI (by simpa using h1), ha, Finset.sum_singleton, Finset.erase_singleton,
          if_pos ⟨rfl, rfl⟩]
      · rw [projOp_of_not (fun h => h1 (h.2 k (Finset.mem_singleton_self k))), neg_zero]
        refine Finset.sum_eq_zero fun i hi => if_neg fun h => ?_
        have h2 := Finset.card_erase_of_mem hi
        rw [h.1, Finset.card_empty] at h2
        have h3 := Finset.card_pos.2 ⟨i, hi⟩
        omega
    rw [dif_of_good hI, coneOp_of_good hI hck, dif_of_good hJ, sum_addC c I k hck, rem_addC hck, smul_add,
      smul_smul, faceSign_mul_self, one_smul, sub_eq_add_neg, ← hsum,
      ← Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl (key l)]
    simp only [Finset.sum_add_distrib, Finset.smul_sum]
    abel

theorem projOp_rem_pair {f : (∀ k, Finset (ι k)) → Ω} {I : ∀ k, Finset (ι k)}
    (hI : Good y I) {T : Finset K} {j : K} (hj : j ∈ T) {i : ι j} (hi : i ∈ I j) (h2 : (I j).card = 2) :
    projOp y c T f (rem I ⟨j, i⟩) = if (∀ m ∈ T, m ≠ j → (I m).card = 1) then f (setC c T I) else 0 := by
  have hcard : (rem I ⟨j, i⟩ j).card = 1 := by rw [rem_apply_self, Finset.card_erase_of_mem hi, h2]
  have hne : ((I j).erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hi, h2]; norm_num
  have hset : setC c T (rem I ⟨j, i⟩) = setC c T I := by
    funext m
    by_cases hm : m ∈ T
    · rw [setC_apply_mem hm, setC_apply_mem hm]
    · rw [setC_apply_not_mem hm, setC_apply_not_mem hm, rem_apply_of_ne i (fun e => hm (by rw [e]; exact hj))]
  by_cases hT : ∀ m ∈ T, m ≠ j → (I m).card = 1
  · rw [if_pos hT, projOp_of_good (good_rem hI hne), hset]
    intro m hm
    by_cases hmj : m = j
    · subst hmj; exact hcard
    · rw [rem_apply_of_ne i hmj]; exact hT m hm hmj
  · rw [if_neg hT, projOp_of_not]
    rintro ⟨-, h⟩
    apply hT
    intro m hm hmj
    have := h m hm
    rwa [rem_apply_of_ne i hmj] at this

theorem dif_projOp (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : (∀ k, Finset (ι k)) → Ω} (hf : Supp y f) (T : Finset K)
    (I : ∀ k, Finset (ι k)) : dif y (projOp y c T f) I = projOp y c T (dif y f) I := by
  by_cases hI : Good y I
  swap
  · rw [dif_of_not hI, projOp_of_not (fun h => hI h.1)]
  rw [dif_of_good hI]
  by_cases hT : ∀ j ∈ T, (I j).card = 1
  · rw [projOp_of_good hI hT, dif_of_good (good_setC hc hI T)]
    have hcards : ∀ m, (I m).card = (setC c T I m).card := by
      intro m
      by_cases hm : m ∈ T
      · rw [setC_apply_mem hm, Finset.card_singleton, hT m hm]
      · rw [setC_apply_not_mem hm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l ∈ T
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hT l hl)
      have h1 : projOp y c T f (rem I ⟨l, a⟩) = 0 := projOp_of_not fun h => by
        have := h.1.1 l
        rw [rem_apply_self, ha, Finset.erase_singleton] at this
        exact Finset.not_nonempty_empty this
      have h2 : f (rem (setC c T I) ⟨l, c l⟩) = 0 := hf _ fun h => by
        have := h.1 l
        rw [rem_apply_self, setC_apply_mem hl, Finset.erase_singleton] at this
        exact Finset.not_nonempty_empty this
      rw [ha, setC_apply_mem hl, Finset.sum_singleton, Finset.sum_singleton, h1, h2, smul_zero, smul_zero]
    · rw [setC_apply_not_mem hl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [faceSign_congr i (setC_apply_not_mem hl).symm hcards]
      congr 1
      by_cases hne : ((I l).erase i).Nonempty
      · rw [projOp_of_good (good_rem hI hne) (fun j hj => by
          rw [rem_apply_of_ne i (fun e => hl (e ▸ hj))]; exact hT j hj), rem_setC i hl]
      · have hbad : ¬ Good y (rem (setC c T I) ⟨l, i⟩) := fun h => hne (by
          have := h.1 l
          rwa [rem_apply_self, setC_apply_not_mem hl] at this)
        rw [projOp_of_not (fun h => hne (by simpa [rem_apply_self] using h.1.1 l)), hf _ hbad]
  · obtain ⟨j, hjT, hj1⟩ : ∃ j ∈ T, (I j).card ≠ 1 := by
      by_contra hne
      exact hT fun j hj => by_contra fun h => hne ⟨j, hj, h⟩
    rw [projOp_of_not (fun h => hT h.2)]
    rw [Finset.sum_eq_single j]
    · by_cases h2 : (I j).card = 2
      · obtain ⟨a, b, hab, hIj⟩ := Finset.card_eq_two.1 h2
        have ha : a ∈ I j := by rw [hIj]; simp
        have hb : b ∈ I j := by rw [hIj]; simp
        have e1 := faceSign_pair hIj hab
        have e2 := faceSign_mul_self I j a
        have e3 : faceSign I j a + faceSign I j b = 0 := by
          linear_combination faceSign I j a * e1 - faceSign I j b * e2
        rw [hIj, Finset.sum_pair hab, projOp_rem_pair hI hjT ha h2, projOp_rem_pair hI hjT hb h2,
          ← add_smul, e3, zero_smul]
      · refine Finset.sum_eq_zero fun i hi => ?_
        rw [projOp_of_not, smul_zero]
        rintro ⟨-, h⟩
        have h3 := h j hjT
        rw [rem_apply_self, Finset.card_erase_of_mem hi] at h3
        have h4 := Finset.card_pos.2 ⟨i, hi⟩
        omega
    · intro l _ hl
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [projOp_of_not, smul_zero]
      rintro ⟨-, h⟩
      exact hj1 (by have := h j hjT; rwa [rem_apply_of_ne i (Ne.symm hl)] at this)
    · intro h; exact absurd (Finset.mem_univ j) h

omit [∀ k, LinearOrder (ι k)] in

theorem projOp_projOp (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (f : (∀ k, Finset (ι k)) → Ω) (T : Finset K) {k : K}
    (hk : k ∉ T) (I : ∀ k, Finset (ι k)) :
    projOp y c T (projOp y c {k} f) I = projOp y c (insert k T) f I := by
  by_cases h : Good y I ∧ ∀ j ∈ insert k T, (I j).card = 1
  · rw [projOp_of_good h.1 (fun j hj => h.2 j (Finset.mem_insert_of_mem hj)),
      projOp_of_good (good_setC hc h.1 T), setC_setC hk, projOp_of_good h.1 h.2]
    intro j hj
    rw [Finset.mem_singleton] at hj
    rw [hj, setC_apply_not_mem hk]
    exact h.2 k (Finset.mem_insert_self _ _)
  · rw [projOp_of_not h]
    by_cases h' : Good y I ∧ ∀ j ∈ T, (I j).card = 1
    · rw [projOp_of_good h'.1 h'.2, projOp_of_not]
      rintro ⟨-, h2⟩
      apply h
      refine ⟨h'.1, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with hj | hj
      · rw [hj]
        have := h2 k (Finset.mem_singleton_self k)
        rwa [setC_apply_not_mem hk] at this
      · exact h'.2 j hj
    · rw [projOp_of_not h']

omit [∀ k, LinearOrder (ι k)] in
theorem projOp_sub (T : Finset K) (a b : (∀ k, Finset (ι k)) → Ω) (I : ∀ k, Finset (ι k)) :
    projOp y c T (fun J => a J - b J) I = projOp y c T a I - projOp y c T b I := by
  by_cases h : Good y I ∧ ∀ j ∈ T, (I j).card = 1
  · rw [projOp_of_good h.1 h.2, projOp_of_good h.1 h.2, projOp_of_good h.1 h.2]
  · rw [projOp_of_not h, projOp_of_not h, projOp_of_not h, sub_zero]

omit [∀ k, LinearOrder (ι k)] in
theorem projOp_empty {f : (∀ k, Finset (ι k)) → Ω} (hf : Supp y f) (I : ∀ k, Finset (ι k)) :
    projOp y c ∅ f I = f I := by
  by_cases h : Good y I
  · rw [projOp_of_good h (by simp)]
    congr 1
  · rw [projOp_of_not (fun h' => h h'.1), hf I h]

omit [∀ k, LinearOrder (ι k)] in
theorem projOp_univ (f : (∀ k, Finset (ι k)) → Ω) {I : ∀ k, Finset (ι k)} (h : ∃ j, (I j).card ≠ 1) :
    projOp y c Finset.univ f I = 0 := by
  obtain ⟨j, hj⟩ := h
  exact projOp_of_not fun h' => hj (h'.2 j (Finset.mem_univ j))

theorem dif_sum (g : K → (∀ k, Finset (ι k)) → Ω) (I : ∀ k, Finset (ι k)) :
    dif y (fun J => ∑ k, g k J) I = ∑ k, dif y (g k) I := by
  by_cases h : Good y I
  · simp only [dif_of_good h, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  · simp [dif_of_not h]

def homot (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : (∀ k, Finset (ι k)) → Ω) (I : ∀ k, Finset (ι k)) : Ω :=
  ∑ k, projOp y c (Finset.univ.filter (· < k)) (coneOp y c k f) I

theorem dif_homot (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : (∀ k, Finset (ι k)) → Ω} (hf : Supp y f)
    (h0 : ∀ J, dif y f J = 0) (I : ∀ k, Finset (ι k)) (hpos : ∃ j, (I j).card ≠ 1) :
    dif y (homot y c f) I = f I := by
  have hcone : ∀ k, dif y (coneOp y c k f) = fun J => f J - projOp y c {k} f J := by
    intro k
    funext J
    have h := dif_coneOp hc hf k J
    have hz : coneOp y c k (dif y f) J = 0 := by
      rw [show dif y f = fun _ => 0 from funext h0]
      unfold coneOp
      split_ifs <;> simp
    rwa [hz, add_zero] at h
  have hterm : ∀ k, dif y (projOp y c (Finset.univ.filter (· < k)) (coneOp y c k f)) I =
      projOp y c (Finset.univ.filter (· < k)) f I - projOp y c (Finset.univ.filter (· ≤ k)) f I := by
    intro k
    have hins : insert k (Finset.univ.filter (· < k)) = Finset.univ.filter (· ≤ k) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.elim (fun e => e ▸ le_rfl) le_of_lt, fun h => (eq_or_lt_of_le h).imp id id⟩
    rw [dif_projOp hc (supp_coneOp k f), hcone k, projOp_sub,
      projOp_projOp hc f _ (by simp), hins]
  unfold homot
  rw [dif_sum, Finset.sum_congr rfl fun k _ => hterm k]
  refine (telescope (fun T => projOp y c T f I) Finset.univ).trans ?_
  show projOp y c ∅ f I - projOp y c Finset.univ f I = f I
  rw [projOp_empty hf, projOp_univ f hpos, sub_zero]

theorem supp_homot (f : (∀ k, Finset (ι k)) → Ω) : Supp y (homot y c f) :=
  fun _ h => Finset.sum_eq_zero fun _ _ => projOp_of_not fun h' => h h'.1

open Classical in

def extC (m : ℕ) (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) : Ω :=
  if h : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = m then t ⟨J, h⟩ else 0

theorem deg_rem {J : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ J k) (hne : ((J k).erase i).Nonempty) :
    ∑ l, ((rem J ⟨k, i⟩ l).card - 1) + 1 = ∑ l, ((J l).card - 1) := by
  have hk := two_le_card hi hne
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    rem_apply_self, Finset.card_erase_of_mem hi,
    Finset.sum_congr rfl fun l hl => by rw [rem_apply_of_ne i (Finset.ne_of_mem_erase hl)]]
  omega

variable (S : Type) [CommRing S] [Algebra S Ω]

theorem cellD_apply (m : ℕ) (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι m → Ω) (J : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (m + 1)) (hJ : CellMeets y J.1) :
    cellD S y m t J = ∑ k, ∑ i ∈ J.1 k, faceSign J.1 k i • extC m t (rem J.1 ⟨k, i⟩) := by
  simp only [cellD, LinearMap.pi_apply, if_pos hJ, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  unfold extC rem
  by_cases h : (∀ l, (Function.update J.1 k ((J.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update J.1 k ((J.1 k).erase i) l).card - 1) = m
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, smul_zero]; rfl

theorem cellD_apply_not (m : ℕ) (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι m → Ω) (J : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (m + 1)) (hJ : ¬ CellMeets y J.1) :
    cellD S y m t J = 0 := by
  simp only [cellD, LinearMap.pi_apply, if_neg hJ, LinearMap.zero_apply]

theorem dif_extC_eq_zero {q : ℕ} {s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (q + 1) → Ω} (hs : cellD S y (q + 1) s = 0)
    (J : ∀ k, Finset (ι k)) : dif y (extC (q + 1) s) J = 0 := by
  by_cases hJ : Good y J
  · rw [dif_of_good hJ]
    by_cases hd : ∑ l, ((J l).card - 1) = q + 1 + 1
    · have h := congrFun hs ⟨J, hJ.1, hd⟩
      rw [cellD_apply S (q + 1) s ⟨J, hJ.1, hd⟩ hJ.2] at h
      exact h
    · refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i hi => ?_
      rw [extC, dif_neg, smul_zero]
      rintro ⟨hne, hdeg⟩
      have := deg_rem hi (by simpa [rem_apply_self] using hne k)
      omega
  · exact dif_of_not hJ

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem extC_mem {m : ℕ} {G : (∀ k, Finset (ι k)) → Submodule S Ω} {s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι m → Ω}
    (hs : s ∈ cellCOf S G m) (J : ∀ k, Finset (ι k)) : extC m s J ∈ G J := by
  unfold extC
  split_ifs with h
  · exact (Submodule.mem_pi.1 hs) ⟨J, h⟩ (Set.mem_univ _)
  · exact zero_mem _

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem supp_extC {m : ℕ} {G : (∀ k, Finset (ι k)) → Submodule S Ω} {s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι m → Ω}
    (hs : s ∈ cellCOf S G m)
    (hbot : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) :
    Supp y (extC m s) := by
  intro J hJ
  unfold extC
  split_ifs with h
  · have hm := (Submodule.mem_pi.1 hs) ⟨J, h⟩ (Set.mem_univ _)
    rw [hbot J h.1 (fun hm' => hJ ⟨h.1, hm'⟩)] at hm
    exact (Submodule.mem_bot S).1 hm
  · rfl

omit [Fintype K] in

theorem G_fill {G : (∀ k, Finset (ι k)) → Submodule S Ω}
    (hins : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I)
    {J : ∀ k, Finset (ι k)} (hJ : ∀ l, (J l).Nonempty) (T : Finset K) :
    G (fun j => if j ∈ T then insert (c j) (J j) else J j) = G J := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert k T hk ih =>
    have hne : ∀ l, ((fun j => if j ∈ T then insert (c j) (J j) else J j) l).Nonempty := by
      intro l
      dsimp only
      split_ifs
      · exact Finset.insert_nonempty _ _
      · exact hJ l
    have e : Function.update (fun j => if j ∈ T then insert (c j) (J j) else J j) k
        (insert (c k) ((fun j => if j ∈ T then insert (c j) (J j) else J j) k)) =
        fun j => if j ∈ insert k T then insert (c j) (J j) else J j := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [hk]
      · rw [Function.update_of_ne hj]; simp [hj]
    rw [← e, hins _ hne k, ih]

theorem homot_mem (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : (∀ k, Finset (ι k)) → Submodule S Ω}
    (hins : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I)
    (hmono : ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
      G I ≤ G I')
    {f : (∀ k, Finset (ι k)) → Ω} (hfG : ∀ J, f J ∈ G J) (J : ∀ k, Finset (ι k)) :
    homot y c f J ∈ G J := by
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases h : Good y J ∧ ∀ j ∈ Finset.univ.filter (· < k), (J j).card = 1
  · rw [projOp_of_good h.1 h.2]
    by_cases h' : Good y (setC c (Finset.univ.filter (· < k)) J) ∧
        c k ∉ setC c (Finset.univ.filter (· < k)) J k
    · rw [coneOp_of_good h'.1 h'.2]
      refine zsmul_mem ?_ _
      have hfill : G (fun j => insert (c j) (J j)) = G J := by
        have := G_fill S hins h.1.1 Finset.univ
        simpa using this
      rw [← hfill]
      refine hmono _ _ (good_addC hc h'.1 k).1 (fun l => ?_) (fun l j hj => ?_) (hfG _)
      · have hs : setC c (Finset.univ.filter (· < k)) J l ⊆ insert (c l) (J l) := by
          by_cases hl : l ∈ Finset.univ.filter (· < k)
          · rw [setC_apply_mem hl]; exact Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)
          · rw [setC_apply_not_mem hl]; exact Finset.subset_insert _ _
        by_cases hlk : l = k
        · subst hlk; rw [addC_apply_self]; exact Finset.insert_subset (Finset.mem_insert_self _ _) hs
        · rw [addC_apply_of_ne c _ hlk]; exact hs
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hc l
        · exact h.1.2 l j hj
    · rw [coneOp_of_not h']; exact zero_mem _
  · rw [projOp_of_not h]; exact zero_mem _

end CellContract

open CellContract in

theorem CellContract.proof : CellContract.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y G c hc hbot hmono hins q s hs hds
  have hf := supp_extC S hs hbot
  have h0 := dif_extC_eq_zero S hds
  have hfG := extC_mem S hs
  refine ⟨fun J => homot y c (extC (q + 1) s) J.1,
    Submodule.mem_pi.2 fun J _ => homot_mem S hc hins hmono hfG J.1, ?_⟩
  funext I
  by_cases hI : CellMeets y I.1
  · have hpos : ∃ j, (I.1 j).card ≠ 1 := by
      by_contra h
      have h1 : ∀ j, (I.1 j).card = 1 := fun j => by_contra fun hj => h ⟨j, hj⟩
      have h2 := I.2.2
      simp [h1] at h2
    have hgood : Good y I.1 := ⟨I.2.1, hI⟩
    have hsI : extC (q + 1) s I.1 = s I := by
      unfold extC
      rw [dif_pos I.2]
      rfl
    rw [cellD_apply S q _ I hI, ← hsI, ← dif_homot hc hf h0 I.1 hpos, dif_of_good hgood]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
    congr 1
    unfold extC
    split_ifs with hcell
    · rfl
    · symm
      have hbad : ¬ Good y (rem I.1 ⟨k, i⟩) := fun hg => hcell ⟨hg.1, by
        have h1 := deg_rem hi (by simpa [rem_apply_self] using hg.1 k)
        have h2 := I.2.2
        omega⟩
      exact supp_homot _ _ hbad
  · rw [cellD_apply_not S q _ I hI]
    have hm := (Submodule.mem_pi.1 hs) I (Set.mem_univ _)
    rw [hbot I.1 I.2.1 hI] at hm
    exact ((Submodule.mem_bot S).1 hm).symm

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
