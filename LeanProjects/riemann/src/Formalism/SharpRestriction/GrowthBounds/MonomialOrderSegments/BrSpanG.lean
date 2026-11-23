import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardFilterValLt

noncomputable section

open MvPolynomial Finset
open Classical

namespace Formalism.MainNotions.G.Joints.PlaneGramSpan

open Formalism.MainNotions.G Formalism.MainNotions.G.Joints

theorem card_val_lt {n h : ℕ} (hh : h ≤ n) : (univ.filter fun m : Fin n => m.val < h).card = h := by
  first | exact GlobalTheory.CardFilterLt.card_filter_val_lt .. | (apply GlobalTheory.CardFilterLt.card_filter_val_lt <;> assumption) | (intros; apply GlobalTheory.CardFilterLt.card_filter_val_lt <;> assumption) | (apply @GlobalTheory.CardFilterLt.card_filter_val_lt <;> assumption) | (intros; apply @GlobalTheory.CardFilterLt.card_filter_val_lt <;> assumption) | (apply @GlobalTheory.CardFilterLt.card_filter_val_lt <;> first | assumption | infer_instance) | exact @GlobalTheory.CardFilterLt.card_filter_val_lt n h hh | exact @GlobalTheory.CardFilterLt.card_filter_val_lt n h | exact @GlobalTheory.CardFilterLt.card_filter_val_lt n

theorem colH_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu c ≤ n := by
  unfold colH
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem colH_zero {n : ℕ} (c : ℤ) : colH (0 : Fin n → ℤ) c = if c ≤ 0 then n else 0 := by
  unfold colH
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun m _ => by simpa using h)]; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _; simpa using h

def oneMu (n N : ℕ) (h : Fin (N + 1) → ℕ) (e : ℤ) : Fin (N + 1) → Fin n → ℤ :=
  fun i m => (if m.val < h i then 1 else 0) - e

theorem colH_oneMu {n N : ℕ} (h : Fin (N + 1) → ℕ) (e : ℤ) (i : Fin (N + 1)) (hh : h i ≤ n) (c : ℤ) :
    colH (oneMu n N h e i) c = if c + e ≤ 0 then n else if c + e = 1 then h i else 0 := by
  unfold colH oneMu
  split_ifs with h1 h2
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro m _; split_ifs <;> omega
  · refine Eq.trans ?_ (card_val_lt hh)
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h3
      by_contra h4
      rw [if_neg h4] at h3
      omega
    · intro h3
      rw [if_pos h3]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _; split_ifs <;> omega

theorem hstrip_one {n : ℕ} (a b : ℕ) (e : ℤ) (hb : b ≤ n) (h1 : a ≤ b) (h2 : b ≤ a + 1) :
    HStrip (fun m : Fin n => (if m.val < a then (1 : ℤ) else 0) - e)
      (fun m : Fin n => (if m.val < b then (1 : ℤ) else 0) - e) (b - a) := by
  refine ⟨fun m => ?_, fun m hm => ?_, ?_⟩
  · show (if m.val < a then (1 : ℤ) else 0) - e ≤ (if m.val < b then (1 : ℤ) else 0) - e
    split_ifs <;> omega
  · show (if m.val + 1 < b then (1 : ℤ) else 0) - e ≤ (if m.val < a then (1 : ℤ) else 0) - e
    split_ifs <;> omega
  · have e1 : ∀ m : Fin n, ((if m.val < b then (1 : ℤ) else 0) - e - ((if m.val < a then (1 : ℤ) else 0) - e)) =
        (if m.val < b then (1 : ℤ) else 0) - (if m.val < a then (1 : ℤ) else 0) := fun m => by ring
    simp only [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, card_val_lt hb, card_val_lt (h1.trans hb)]
    push_cast [Nat.cast_sub h1]
    ring

def onePath {n N : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath n N LL d) (c : ℤ) :
    PPath n N LL (fun i => if IsUsed P.mu c i then 1 else 0) where
  mu := oneMu n N (fun i => colH (P.mu i) c) (if 1 ≤ c then 0 else 1)
  zero := by
    funext m
    show (if m.val < colH (P.mu 0) c then (1 : ℤ) else 0) - (if 1 ≤ c then 0 else 1) = 0
    rw [P.zero, colH_zero]
    have := m.2
    split_ifs <;> omega
  dom := by
    intro i m m' hmm
    have h0 : m.val ≤ m'.val := hmm
    show (if m'.val < colH (P.mu i) c then (1 : ℤ) else 0) - _ ≤ (if m.val < colH (P.mu i) c then (1 : ℤ) else 0) - _
    split_ifs <;> omega
  step := by
    intro i
    have hstep := P.step i
    by_cases hv : LL.vec i = true
    · rw [if_pos hv] at hstep ⊢
      have h1 := colH_strip hstep.1 c
      have h2 := strip_le_one hstep (P.dom _) c
      have h3 := hstrip_one (n := n) (colH (P.mu i.castSucc) c) (colH (P.mu i.succ) c) (if 1 ≤ c then 0 else 1)
        (colH_le _ _) (by omega) (by omega)
      have h4 : (if IsUsed P.mu c i then 1 else 0) = colH (P.mu i.succ) c - colH (P.mu i.castSucc) c := by
        unfold IsUsed
        split_ifs with h <;> omega
      rw [h4]; exact h3
    · rw [if_neg hv] at hstep ⊢
      have h1 := colH_strip hstep.1 c
      have h2 := strip_le_one hstep (P.dom _) c
      have h3 := hstrip_one (n := n) (colH (P.mu i.succ) c) (colH (P.mu i.castSucc) c) (if 1 ≤ c then 0 else 1)
        (colH_le _ _) (by omega) (by omega)
      have h4 : (if IsUsed P.mu c i then 1 else 0) = colH (P.mu i.castSucc) c - colH (P.mu i.succ) c := by
        unfold IsUsed
        split_ifs with h <;> omega
      rw [h4]; exact h3

theorem colH_onePath {n N : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath n N LL d) (c : ℤ)
    (i : Fin (N + 1)) (c' : ℤ) :
    colH ((onePath P c).mu i) c' = if c' + (if 1 ≤ c then 0 else 1) ≤ 0 then n
      else if c' + (if 1 ≤ c then 0 else 1) = 1 then colH (P.mu i) c else 0 :=
  colH_oneMu (fun i => colH (P.mu i) c) _ i (colH_le _ _) c'

theorem colStep_congr {n : ℕ} {P : Type*} [CommRing P] {c c' : ℤ} (hc : 1 ≤ c ↔ 1 ≤ c') (a b : ℕ)
    (x : Fin n → P) (K : Finset (Fin n) → P) : colStep c a b x K = colStep c' a b x K := by
  unfold colStep
  by_cases h : 1 ≤ c
  · simp only [if_pos h, if_pos (hc.1 h)]
  · simp only [if_neg h, if_neg (fun x => h (hc.2 x))]

theorem Kcol_ge (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) (h : ¬ j < N) :
    Kcol R mu c (j + 1) = Kcol R mu c j := by
  rw [Kcol, dif_neg h]

theorem Kcol_congr (R : Type*) [CommRing R] {N n : ℕ} (mu mu' : Fin (N + 1) → Fin n → ℤ) (c c' : ℤ)
    (hc : 1 ≤ c ↔ 1 ≤ c') (hh : ∀ i, colH (mu i) c = colH (mu' i) c') :
    ∀ j, Kcol R mu c j = Kcol R mu' c' j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : j < N
    · rw [Kcol_succ R mu c j h, Kcol_succ R mu' c' j h, ih, hh, hh, colStep_congr hc]
    · rw [Kcol_ge R mu c j h, Kcol_ge R mu' c' j h, ih]

theorem Kcol_unused (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ)
    (hun : ∀ i : Fin N, ¬ IsUsed mu c i) : ∀ j, Kcol R mu c j = extOne := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : j < N
    · have h3 : colH (mu (⟨j, h⟩ : Fin N).castSucc) c = colH (mu (⟨j, h⟩ : Fin N).succ) c := not_not.1 (hun ⟨j, h⟩)
      rw [Kcol_succ R mu c j h, ih, h3, colStep_same]
    · rw [Kcol_ge R mu c j h, ih]

theorem Psi_one (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c0 : ℤ)
    (hc0 : c0 ∈ colRange mu) (hun : ∀ c, c ≠ c0 → ∀ i : Fin N, ¬ IsUsed mu c i) (I : ℤ → Finset (Fin n))
    (hI : ∀ c, c ≠ c0 → I c = ∅) : Psi R mu I = Kcol R mu c0 N (I c0) := by
  unfold Psi
  rw [Finset.prod_eq_single c0]
  · intro c _ hc
    rw [Kcol_unused R mu c (hun c hc), hI c hc]
    simp [extOne]
  · intro h; exact absurd hc0 h

theorem colH_const {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (hun : ∀ i : Fin N, ¬ IsUsed mu c i) :
    ∀ i : Fin (N + 1), colH (mu i) c = colH (mu 0) c := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← ih]; exact (not_not.1 (hun i)).symm

theorem valS_zero' {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) :
    valS LL S (0 : MvPolynomial (ι × Fin n) R) = ⊤ := by
  unfold valS sDegs
  simp

section ColEst

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem col_est (h3b : Formalism.MainNotions.PlaneGramData.PathSpanAtRing O) {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ}
    (P : PPath r N LL d) (c : ℤ) (J : Finset (Fin r))
    (hJ : J.card = if 1 ≤ c then colH (pEnd P.mu) c else r - colH (pEnd P.mu) c) (i : Fin N) :
    ((((if 1 ≤ c ∧ colH (P.mu i.succ) c = r then 1 else 0) -
        (if c ≤ 0 ∧ colH (P.mu i.succ) c < r then 1 else 0) : ℤ)) : WithTop ℤ)
      ≤ valS LL {j | j ≤ i} (Kcol (KK O) P.mu c N J) := by
  have hr : 0 < r := NeZero.pos r
  by_cases hun : ∀ i : Fin N, ¬ IsUsed P.mu c i
  · have hc := colH_const P.mu c hun i.succ
    rw [P.zero, colH_zero] at hc
    have h0 : ((if 1 ≤ c ∧ colH (P.mu i.succ) c = r then 1 else 0) -
        (if c ≤ 0 ∧ colH (P.mu i.succ) c < r then 1 else 0) : ℤ) = 0 := by
      rw [hc]
      by_cases h1 : c ≤ 0
      · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; rfl
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]; rfl
    rw [h0, Kcol_unused _ _ _ hun]
    unfold extOne
    split_ifs
    · rw [valS_one]; rfl
    · rw [valS_zero']; exact le_top
  · simp only [not_forall, not_not] at hun
    obtain ⟨i0, hi0⟩ := hun
    obtain ⟨e, he⟩ : ∃ e : ℤ, e = if 1 ≤ c then 0 else 1 := ⟨_, rfl⟩
    have he' : (e = 0 ∧ 1 ≤ c) ∨ (e = 1 ∧ c ≤ 0) := by
      by_cases h : 1 ≤ c
      · left; rw [he, if_pos h]; exact ⟨rfl, h⟩
      · right; rw [he, if_neg h]; exact ⟨rfl, by omega⟩
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℤ, c0 = 1 - e := ⟨_, rfl⟩
    have hH : ∀ (i : Fin (N + 1)) (c' : ℤ), colH ((onePath P c).mu i) c' =
        if c' + e ≤ 0 then r else if c' + e = 1 then colH (P.mu i) c else 0 := by
      intro i c'; rw [he]; exact colH_onePath P c i c'
    have hH0 : ∀ i, colH ((onePath P c).mu i) c0 = colH (P.mu i) c := by
      intro i
      rw [hH, if_neg (by omega), if_pos (by omega)]
    have hused : IsUsed (onePath P c).mu c0 i0 := by
      unfold IsUsed; rw [hH0, hH0]; exact hi0
    have hmem := col_clause3 (onePath P c) c0 i0 hused
    have hun' : ∀ c', c' ≠ c0 → ∀ i : Fin N, ¬ IsUsed (onePath P c).mu c' i := by
      intro c' hc' i
      unfold IsUsed
      rw [hH, hH, if_neg (by omega : ¬ c' + e = 1), if_neg (by omega : ¬ c' + e = 1)]
      exact not_not.2 rfl
    have hc1 : 1 ≤ c ↔ 1 ≤ c0 := by omega
    set I' : ℤ → Finset (Fin r) := fun c' => if c' = c0 then J else ∅ with hI'
    have hSt : IsSt (onePath P c).mu I' := by
      refine ⟨fun c' hc' => ?_, fun c' => ?_, fun c' t => ?_⟩
      · show (if c' = c0 then J else ∅) = ∅
        rw [if_neg]; rintro rfl; exact hc' hmem
      · show (if c' = c0 then J else ∅).card = _
        have hE : pEnd (onePath P c).mu = (onePath P c).mu (Fin.last N) := rfl
        rw [hE, hH]
        by_cases h : c' = c0
        · rw [if_pos h, hJ, h, if_neg (by omega : ¬ c0 + e ≤ 0), if_pos (by omega : c0 + e = 1)]
          by_cases hc : 1 ≤ c
          · rw [if_pos hc, if_pos (hc1.1 hc)]; rfl
          · rw [if_neg hc, if_neg (fun x => hc (hc1.2 x))]; rfl
        · rw [if_neg h, Finset.card_empty]
          split_ifs <;> omega
      · refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
        by_cases h1 : 1 ≤ c'
        · have : tabCol I' (c' + 1) = ∅ := by
            unfold tabCol; rw [if_pos (by omega)]; exact if_neg (by omega)
          rw [this]; exact Finset.empty_subset _
        · by_cases h2 : c' = c0
          · have : tabCol I' (c' + 1) = ∅ := by
              unfold tabCol; rw [if_pos (by omega)]; exact if_neg (by omega)
            rw [this]; exact Finset.empty_subset _
          · have : tabCol I' c' = univ := by
              unfold tabCol; rw [if_neg h1]
              show univ \ (if c' = c0 then J else ∅) = univ
              rw [if_neg h2]; simp
            rw [this]; exact Finset.subset_univ _
    have key := (h3b N r LL _).2 (onePath P c) I' hSt i
    rw [Psi_one O (onePath P c).mu c0 hmem hun' I' (fun c' h => if_neg h)] at key
    have hJ' : I' c0 = J := if_pos rfl
    rw [hJ', ← Kcol_congr O P.mu (onePath P c).mu c c0 hc1 (fun i => (hH0 i).symm) N] at key
    rw [← StandardMonomialSpace.lift_Kcol_map (algebraMap O (KK O)) P.mu c N J,
      StandardMonomialSpace.valS_map _ (IsFractionRing.injective O (KK O))]
    refine le_trans (le_of_eq ?_) key
    congr 1
    show _ = (if (lastIdx r).val < colH (P.mu i.succ) c then (1 : ℤ) else 0) - (if 1 ≤ c then 0 else 1)
    have hl : (lastIdx r).val = r - 1 := rfl
    have hle := colH_le (P.mu i.succ) c
    rw [hl]
    split_ifs <;> omega

end ColEst

theorem sum_colVal (T x : ℤ) (h1 : -T ≤ x) (h2 : x ≤ T) :
    ∑ c ∈ Finset.Icc (-T) T, ((if 1 ≤ c ∧ c ≤ x then (1 : ℤ) else 0) - (if c ≤ 0 ∧ x < c then (1 : ℤ) else 0)) = x := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have e1 : (Finset.Icc (-T) T).filter (fun c => 1 ≤ c ∧ c ≤ x) = Finset.Icc 1 x := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
    · intro h; exact h.2
    · intro h; exact ⟨⟨by omega, by omega⟩, h⟩
  have e2 : (Finset.Icc (-T) T).filter (fun c => c ≤ 0 ∧ x < c) = Finset.Ioc x 0 := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; constructor
    · intro h; exact ⟨h.2.2, h.2.1⟩
    · intro h; exact ⟨⟨by omega, by omega⟩, h.2, h.1⟩
  rw [e1, e2, Int.card_Icc, Int.card_Ioc]
  omega

theorem colH_eq_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hd : Dominant mu) (c : ℤ) :
    colH mu c = n ↔ c ≤ mu (lastIdx n) := by
  unfold colH
  constructor
  · intro h
    have h1 : (univ.filter fun m => c ≤ mu m) = univ := by
      apply Finset.eq_univ_of_card; rw [h]; simp
    have := Finset.mem_univ (lastIdx n)
    rw [← h1] at this
    exact (Finset.mem_filter.1 this).2
  · intro h
    rw [Finset.filter_true_of_mem]
    · simp
    · intro m _
      refine h.trans (hd ?_)
      show m.val ≤ n - 1
      have := m.2; omega

theorem stage_identity {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d)
    (i : Fin (N + 1)) :
    P.mu i (lastIdx r) = ∑ c ∈ colRange P.mu, ((if 1 ≤ c ∧ colH (P.mu i) c = r then (1 : ℤ) else 0) -
      (if c ≤ 0 ∧ colH (P.mu i) c < r then (1 : ℤ) else 0)) := by
  have hT := abs_le_alt P.mu i (lastIdx r)
  have h1 := neg_abs_le (P.mu i (lastIdx r))
  have h2 := le_abs_self (P.mu i (lastIdx r))
  rw [← sum_colVal (∑ i, ∑ m, |P.mu i m|) (P.mu i (lastIdx r)) (by linarith) (by linarith)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h3 := colH_eq_iff (P.dom i) c
  have h4 := colH_le (P.mu i) c
  have h5 : colH (P.mu i) c < r ↔ P.mu i (lastIdx r) < c := by
    constructor
    · intro h; by_contra h'; exact absurd (h3.2 (not_lt.1 h')) (by omega)
    · intro h; by_contra h'; exact absurd (h3.1 (by omega)) (by omega)
  simp only [h3, h5]

theorem twistSub_empty {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (j : Fin n)
    (F : MvPolynomial (ι × Fin n) R) :
    twistSub LL (∅ : Set ι) j F = MvPolynomial.map (coefL R n) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [twistSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [twistSub]

theorem valS_empty_nonneg {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι)
    (F : MvPolynomial (ι × Fin n) R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LL (∅ : Set ι) F := by
  rw [le_valuation_iff_twist_order]
  intro m
  rw [twistSub_empty, coeff_map]
  exact LGe_C _

theorem valS_empty_le {R : Type} [Field R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι)
    (F : MvPolynomial (ι × Fin n) R) (hF : F ≠ 0) (th : ℤ) (h : ((th : ℤ) : WithTop ℤ) ≤ valS LL (∅ : Set ι) F) :
    th ≤ 0 := by
  have := glCoord_nontrivial R n
  rw [le_valuation_iff_twist_order] at h
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hF
  have h1 := h m
  rw [twistSub_empty, coeff_map] at h1
  refine h1 0 ?_
  rw [Finsupp.mem_support_iff]
  show (LaurentPolynomial.C (((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C)
    (F.coeff m))).coeff 0 ≠ 0
  rw [LaurentPolynomial.C_apply]
  simp only [if_true]
  exact (map_ne_zero _).2 hm

section Lift

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_lift {σ : Type} (F : MvPolynomial σ (KK O)) (h : ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o) :
    ∃ F0 : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) F0 = F := by
  choose o ho using h
  refine ⟨∑ m ∈ F.support, monomial m (o m), ?_⟩
  rw [map_sum]
  simp only [map_monomial, ← ho]
  exact F.support_sum_monomial_coeff

theorem mem_Pol_map {ι : Type} {r : ℕ} (d : ι → ℕ) (F0 : MvPolynomial (ι × Fin r) O) :
    MvPolynomial.map (algebraMap O (KK O)) F0 ∈ Pol (KK O) r d ↔ F0 ∈ Pol O r d := by
  unfold Pol
  rw [mem_restrictSupport_iff, mem_restrictSupport_iff,
    support_map_of_injective _ (IsFractionRing.injective O (KK O))]

theorem comb_of_span {ι : Type} [Fintype ι] {σ : Type} (Ψ0 : ι → MvPolynomial σ O) (s : Set ι)
    (F0 : MvPolynomial σ O) (h : F0 ∈ Submodule.span O (Ψ0 '' s)) :
    ∃ l : ι → O, (∀ b, l b ≠ 0 → b ∈ s) ∧ MvPolynomial.map (algebraMap O (KK O)) F0 =
      ∑ b, algebraMap O (KK O) (l b) • MvPolynomial.map (algebraMap O (KK O)) (Ψ0 b) := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination O).1 h
  refine ⟨fun b => l b, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported O l).1 hl (Finsupp.mem_support_iff.2 hb)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • Ψ0 i) (fun i => zero_smul _ _), map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C]

theorem polSet_finite {N r : ℕ} (d : Fin N → ℕ) : {m : Fin N × Fin r →₀ ℕ | ∀ i, multideg m i = d i}.Finite := by
  refine (Set.finite_Icc (0 : Fin N × Fin r →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun x => d x.1)).subset ?_
  intro m hm
  refine ⟨fun x => Nat.zero_le _, fun x => ?_⟩
  show m x ≤ d x.1
  rw [← hm x.1]
  unfold multideg
  exact Finset.single_le_sum (f := fun c => m (x.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x.2)

abbrev Idx (N r : ℕ) (LL : Letters (Fin N)) (d : Fin N → ℕ) : Type :=
  {x : PPath r N LL d × (ℤ → Finset (Fin r)) // IsSt x.1.mu x.2}

theorem psiO_mem (h3a : Formalism.MainNotions.PlaneGramData.PathColumnBasisAtRing O) {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ}
    (x : Idx N r LL d) : Psi O x.1.1.mu x.1.2 ∈ Pol O r d := by
  rw [← (h3a N r LL d).2]
  exact Submodule.subset_span ⟨x.1.1, x.1.2, x.2, rfl⟩

theorem idx_finite (h3a : Formalism.MainNotions.PlaneGramData.PathColumnBasisAtRing O) (N r : ℕ) [NeZero r] (LL : Letters (Fin N)) (d : Fin N → ℕ) :
    Finite (Idx N r LL d) := by
  have hli := (h3a N r LL d).1
  set W : Submodule O (MvPolynomial (Fin N × Fin r) O) :=
    Submodule.span O ((fun m => monomial m (1 : O)) '' {m : Fin N × Fin r →₀ ℕ | ∀ i, multideg m i = d i}) with hW
  have hN : IsNoetherian O W := isNoetherian_of_fg_of_noetherian W (Submodule.fg_span ((polSet_finite d).image _))
  have hsub : ∀ F ∈ Pol O r d, F ∈ W := by
    intro F hF
    rw [← F.support_sum_monomial_coeff]
    refine Submodule.sum_mem _ fun m hm => ?_
    have h1 : monomial m (F.coeff m) = F.coeff m • monomial m (1 : O) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
    exact ((mem_restrictSupport_iff O).1 hF) (Finset.mem_coe.2 hm)
  have hli' : LinearIndependent O (fun x : Idx N r LL d =>
      (⟨Psi O x.1.1.mu x.1.2, hsub _ (psiO_mem h3a x)⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  exact hli'.finite_of_isNoetherian

theorem li_K (h3a : Formalism.MainNotions.PlaneGramData.PathColumnBasisAtRing O) (N r : ℕ) [NeZero r] (LL : Letters (Fin N)) (d : Fin N → ℕ) :
    LinearIndependent (KK O) (fun x : Idx N r LL d => Psi (KK O) x.1.1.mu x.1.2) := by
  have hli := (h3a N r LL d).1
  have h1 := hli.map' (MvPolynomial.mapAlgHom (σ := Fin N × Fin r) (Algebra.ofId O (KK O))).toLinearMap
    (LinearMap.ker_eq_bot.2 (MvPolynomial.map_injective _ (IsFractionRing.injective O (KK O))))
  have h2 : LinearIndependent O (fun x : Idx N r LL d => Psi (KK O) x.1.1.mu x.1.2) := by
    have e : (fun x : Idx N r LL d => Psi (KK O) x.1.1.mu x.1.2) =
        (⇑(MvPolynomial.mapAlgHom (σ := Fin N × Fin r) (Algebra.ofId O (KK O))).toLinearMap ∘
          fun x : Idx N r LL d => Psi O x.1.1.mu x.1.2) := by
      funext x
      exact (StandardMonomialSpace.Psi_map (algebraMap O (KK O)) x.1.1.mu x.1.2).symm
    rw [e]; exact h1
  exact (LinearIndependent.iff_fractionRing O (KK O)).1 h2

theorem psiK_mem (h3a : Formalism.MainNotions.PlaneGramData.PathColumnBasisAtRing O) {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ}
    (x : Idx N r LL d) : Psi (KK O) x.1.1.mu x.1.2 ∈ Pol (KK O) r d ∧
      ∀ m, ∃ o : O, (Psi (KK O) x.1.1.mu x.1.2).coeff m = algebraMap O (KK O) o := by
  rw [← StandardMonomialSpace.Psi_map (algebraMap O (KK O))]
  exact ⟨(mem_Pol_map d _).2 (psiO_mem h3a x), fun m => ⟨_, coeff_map _ _ _⟩⟩

theorem span_all (h3a : Formalism.MainNotions.PlaneGramData.PathColumnBasisAtRing O) {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ}
    [Fintype (Idx N r LL d)] (F : MvPolynomial (Fin N × Fin r) (KK O)) (hF : F ∈ Pol (KK O) r d)
    (hint : ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o) :
    ∃ l : Idx N r LL d → O, F = ∑ b, algebraMap O (KK O) (l b) • Psi (KK O) b.1.1.mu b.1.2 := by
  obtain ⟨F0, rfl⟩ := exists_lift F hint
  have h0 : F0 ∈ Pol O r d := (mem_Pol_map d F0).1 hF
  rw [← (h3a N r LL d).2] at h0
  have h1 : F0 ∈ Submodule.span O ((fun x : Idx N r LL d => Psi O x.1.1.mu x.1.2) '' Set.univ) := by
    refine Submodule.span_mono ?_ h0
    rintro G ⟨P, I, hI, rfl⟩
    exact ⟨⟨(P, I), hI⟩, Set.mem_univ _, rfl⟩
  obtain ⟨l, -, hl⟩ := comb_of_span _ _ F0 h1
  refine ⟨l, ?_⟩
  rw [hl]
  exact Finset.sum_congr rfl fun b _ => by rw [StandardMonomialSpace.Psi_map]

theorem withBot_le_int (x : WithBot ℤ) : ∃ M : ℤ, x ≤ (M : WithBot ℤ) := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe z => exact ⟨z, le_rfl⟩

theorem span_mem (h3b : Formalism.MainNotions.PlaneGramData.PathSpanAtRing O) {N r : ℕ} [NeZero r] {LL : Letters (Fin N)} {d : Fin N → ℕ}
    [Fintype (Idx N r LL d)] (F : MvPolynomial (Fin N × Fin r) (KK O)) (hF : F ∈ Pol (KK O) r d)
    (hint : ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o) (th : Fin N → ℤ)
    (hth : ∀ i : Fin N, ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} F) :
    ∃ l : Idx N r LL d → O, (∀ b, l b ≠ 0 → ∀ i : Fin N, th i ≤ b.1.1.mu i.succ (lastIdx r)) ∧
      F = ∑ b, algebraMap O (KK O) (l b) • Psi (KK O) b.1.1.mu b.1.2 := by
  obtain ⟨F0, rfl⟩ := exists_lift F hint
  have h0 : F0 ∈ Pol O r d := (mem_Pol_map d F0).1 hF
  choose M hM using fun i : Fin N => withBot_le_int (lam1S LL {j | j ≤ i} F0)
  have hA := (h3b N r LL d).1 th M
  have h1 : F0 ∈ {G : MvPolynomial (Fin N × Fin r) O | G ∈ Pol O r d ∧ ∀ i : Fin N,
      ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧ lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)} := by
    refine ⟨h0, fun i => ⟨?_, hM i⟩⟩
    have := hth i
    rwa [StandardMonomialSpace.valS_map _ (IsFractionRing.injective O (KK O))] at this
  unfold Formalism.MainNotions.CovariantDegrees.A3at at hA
  rw [hA] at h1
  have h2 : F0 ∈ Submodule.span O ((fun x : Idx N r LL d => Psi O x.1.1.mu x.1.2) ''
      {b | ∀ i : Fin N, th i ≤ b.1.1.mu i.succ (lastIdx r)}) := by
    refine Submodule.span_mono ?_ h1
    rintro G ⟨P, I, hI, hc, rfl⟩
    exact ⟨⟨(P, I), hI⟩, fun i => (hc i).1, rfl⟩
  obtain ⟨l, hl1, hl⟩ := comb_of_span _ _ F0 h2
  refine ⟨l, hl1, ?_⟩
  rw [hl]
  exact Finset.sum_congr rfl fun b _ => by rw [StandardMonomialSpace.Psi_map]

end Lift

theorem sum_fin_equiv {M : Type*} [AddCommMonoid M] (s : Finset ℤ) (f : ℤ → M) :
    ∑ k : Fin s.card, f ((s.equivFin.symm k).1) = ∑ c ∈ s, f c := by
  rw [← Finset.sum_coe_sort s f]
  exact Fintype.sum_equiv s.equivFin.symm _ _ (fun _ => rfl)

theorem prod_fin_equiv {M : Type*} [CommMonoid M] (s : Finset ℤ) (f : ℤ → M) :
    ∏ k : Fin s.card, f ((s.equivFin.symm k).1) = ∏ c ∈ s, f c := by
  rw [← Finset.prod_coe_sort s f]
  exact Fintype.prod_equiv s.equivFin.symm _ _ (fun _ => rfl)

end Formalism.MainNotions.G.Joints.PlaneGramSpan
