import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A3comb

theorem idx_empty {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (M : ℤ)
    (hM : ∀ m, |μ m| ≤ M) (c : ℤ) (hc : c ∉ Finset.Icc (-M) M) : I c = ∅ := by
  have key := hI c
  rw [Finset.mem_Icc] at hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext x
    exact x.elim0
  · have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, hn⟩)
    rw [← Finset.card_eq_zero, key]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      unfold colHeight
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _
      have := hM m
      rw [abs_le] at this
      omega
    · rw [if_neg h1]
      have hall : colHeight μ c = n := by
        unfold colHeight
        rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
        intro m _
        have := hM m
        rw [abs_le] at this
        omega
      omega

theorem exists_bound {n : ℕ} (μ : Fin n → ℤ) : ∃ M : ℤ, ∀ m, |μ m| ≤ M := ⟨∑ m, |μ m|, fun m =>
  Finset.single_le_sum (f := fun m => |μ m|) (fun i _ => abs_nonneg _) (Finset.mem_univ m)⟩

private theorem ncard_eq_filter_lemma {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ)
    (hS : ∀ c, c ∉ S → I c = ∅) (m : Fin n) (p : ℤ → Prop) [DecidablePred p] :
    ({c : ℤ | p c ∧ m ∈ I c}.ncard : ℤ) = ((S.filter fun c => p c ∧ m ∈ I c).card : ℤ) := by
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hcS
    rw [hS c hcS] at h2
    simp at h2
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩

theorem idxWeight_eq {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (m : Fin n) :
    idxWeight I m = ∑ c ∈ S, (if m ∈ I c then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
  unfold idxWeight
  rw [ncard_eq_filter_lemma I S hS m (fun c => 1 ≤ c), ncard_eq_filter_lemma I S hS m (fun c => c ≤ 0),
    Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hm : m ∈ I c
  · by_cases hc : 1 ≤ c
    · have h0 : ¬ c ≤ 0 := by omega
      simp [hm, hc, h0]
    · have h0 : c ≤ 0 := by omega
      simp [hm, hc, h0]
  · simp [hm]

theorem weight_torus {n : ℕ} (isVec : ℕ → Bool) (e : ℕ × Fin n →₀ ℕ) (m : Fin n) :
    Finsupp.weight (torusW isVec) e m =
      Finsupp.weight
        (fun x : ℕ × Fin n => if x.2 = m then (if isVec x.1 then (1 : ℤ) else -1) else 0) e := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x.2 = m
  · subst hx
    by_cases hv : isVec x.1 <;> simp [torusW, hv]
  · have hx' : m ≠ x.2 := fun h => hx h.symm
    by_cases hv : isVec x.1 <;> simp [torusW, hv, hx, hx', Pi.single_apply]

end A3comb

open A3comb in
theorem psi_weight : PsiWeight := by
  intro R _ n N isVec B μ I hp hI
  have hmon : ∀ (d : ℕ × Fin n →₀ ℕ) (r : R), IsWeightedHomogeneous (torusW isVec)
      (MvPolynomial.monomial d r) (Finsupp.weight (torusW isVec) d) :=
    fun d r => MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
  have hXw : ∀ x : ℕ × Fin n, IsWeightedHomogeneous (torusW isVec)
      (X x : MvPolynomial (ℕ × Fin n) R) (torusW isVec x) := by
    intro x
    have := hmon (Finsupp.single x 1) 1
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, one_smul] at this
    exact this
  have wedgeW : ∀ (c : ℤ) (k : ℕ) (J : Finset (Fin n)) (m : Fin n), m ∈ J →
      (isVec k == decide (1 ≤ c)) = true →
      (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) =
        (fun a => if a ∈ J.erase m then (if 1 ≤ c then (1 : ℤ) else -1) else 0) +
          torusW isVec (k, m) := by
    intro c k J m hm hup
    funext a
    simp only [Pi.add_apply, torusW, ite_apply, Finset.mem_erase, Pi.single_apply, Pi.neg_apply]
    by_cases hc : 1 ≤ c
    · simp only [if_pos hc, decide_eq_true hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
    · simp only [if_neg hc, decide_eq_false hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
  have contrW : ∀ (c : ℤ) (k : ℕ) (J : Finset (Fin n)) (m : Fin n), m ∉ J →
      ¬ (isVec k == decide (1 ≤ c)) = true →
      (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) =
        torusW isVec (k, m) +
          (fun a => if a ∈ insert m J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
    intro c k J m hm hup
    funext a
    simp only [Pi.add_apply, torusW, ite_apply, Finset.mem_insert, Pi.single_apply, Pi.neg_apply]
    by_cases hc : 1 ≤ c
    · simp only [if_pos hc, decide_eq_true hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
    · simp only [if_neg hc, decide_eq_false hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
  have key : ∀ c : ℤ, ∀ k : ℕ, ∀ J : Finset (Fin n),
      IsWeightedHomogeneous (torusW isVec)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k J)
        (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
    intro c k
    induction k with
    | zero =>
      intro J
      simp only [pathWord, oneF]
      by_cases hJ : J = ∅
      · subst hJ
        rw [if_pos rfl]
        have h0 : (fun a : Fin n => if a ∈ (∅ : Finset (Fin n)) then
            (if 1 ≤ c then (1 : ℤ) else -1) else 0) = 0 := by
          funext a
          simp
        rw [h0]
        have := hmon 0 1
        rw [map_zero] at this
        exact this
      · rw [if_neg hJ]
        exact (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.zero_mem _)
    | succ k ih =>
      intro J
      simp only [pathWord]
      by_cases hcol : colHeight (μ (k + 1)) c = colHeight (μ k) c
      · rw [if_pos hcol]
        exact ih J
      · rw [if_neg hcol]
        unfold stepF
        by_cases hup : (isVec k == decide (1 ≤ c)) = true
        · rw [if_pos hup]
          unfold wedgeF
          beta_reduce
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]
          refine zsmul_mem ?_ _
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
          rw [wedgeW c k J m hm hup]
          exact (ih (J.erase m)).mul (hXw (k, m))
        · rw [if_neg hup]
          unfold contrF
          beta_reduce
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]
          refine zsmul_mem ?_ _
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
          rw [contrW c k J m (Finset.mem_compl.mp hm) hup]
          exact (hXw (k, m)).mul (ih (insert m J))
  obtain ⟨T, hb⟩ : ∃ T : ℤ, ∀ k ≤ N, ∀ m, |μ k m| ≤ T := by
    refine ⟨∑ k ∈ range (N + 1), ∑ m, |μ k m|, fun k hk m => ?_⟩
    calc |μ k m| ≤ ∑ m', |μ k m'| :=
          Finset.single_le_sum (f := fun m' => |μ k m'|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ m)
      _ ≤ ∑ k' ∈ range (N + 1), ∑ m', |μ k' m'| :=
          Finset.single_le_sum (f := fun k' => ∑ m', |μ k' m'|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
  have hS : ∀ c, c ∉ Finset.Icc (-T) T → I c = ∅ := fun c hc => idx_empty hI T (hb N le_rfl) c hc
  have hone : ∀ c, c ∉ Finset.Icc (-T) T → ∀ k ≤ N,
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k = oneF := by
    intro c hc k
    induction k with
    | zero =>
      intro _
      simp only [pathWord]
    | succ k ih =>
      intro hk
      rw [Finset.mem_Icc] at hc
      have hcol : colHeight (μ (k + 1)) c = colHeight (μ k) c := by
        by_cases hcT : T < c
        · have e : ∀ k' ≤ N, colHeight (μ k') c = 0 := by
            intro k' hk'
            unfold colHeight
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro m _
            have := hb k' hk' m
            rw [abs_le] at this
            omega
          rw [e (k + 1) hk, e k (by omega)]
        · have e : ∀ k' ≤ N, colHeight (μ k') c = n := by
            intro k' hk'
            unfold colHeight
            rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
            intro m _
            have := hb k' hk' m
            rw [abs_le] at this
            omega
          rw [e (k + 1) hk, e k (by omega)]
      simp only [pathWord]
      rw [if_pos hcol]
      exact ih (by omega)
  have hsupp : Function.mulSupport (fun c => pathWord isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)) ⊆ ↑(Finset.Icc (-T) T) := by
    intro c hc
    rw [Function.mem_mulSupport] at hc
    by_contra hcS
    apply hc
    rw [hone c hcS N le_rfl, hS c hcS]
    simp [oneF]
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod (Finset.Icc (-T) T) _ _
    (fun c _ => key c N (I c))
  convert hprod using 1
  funext a
  rw [Finset.sum_apply, idxWeight_eq I (Finset.Icc (-T) T) hS a]

namespace A3comb

theorem sum_idxWeight {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (F : Finset (Fin n)) :
    ∑ m ∈ F, idxWeight I m =
      ∑ c ∈ S, (if 1 ≤ c then (1 : ℤ) else -1) * ((F.filter fun m => m ∈ I c).card : ℤ) := by
  simp_rw [idxWeight_eq I S hS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∈ I c <;> simp [hm]

private theorem card_lt_lemma (n k : ℕ) (hk : k ≤ n) :
    (univ.filter fun m : Fin n => m.val < k).card = k := by
  have e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = range k := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]

private theorem lt_colHeight_iff_lemma {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    m.val < colHeight μ c ↔ c ≤ μ m := by
  have hmn := m.isLt
  unfold colHeight
  constructor
  · intro hm
    by_contra hc
    have hsub : (univ.filter fun m' : Fin n => c ≤ μ m') ⊆
        univ.filter fun m' : Fin n => m'.val < m.val := by
      intro m' hm'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      by_contra hle
      have := h (Fin.le_iff_val_le_val.mpr (by omega : m.val ≤ m'.val))
      omega
    have h1 := Finset.card_le_card hsub
    rw [card_lt_lemma n m.val (by omega)] at h1
    omega
  · intro hc
    have hsub : (univ.filter fun m' : Fin n => m'.val < m.val + 1) ⊆
        univ.filter fun m' : Fin n => c ≤ μ m' := by
      intro m' hm'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      exact le_trans hc (h (Fin.le_iff_val_le_val.mpr (by omega : m'.val ≤ m.val)))
    have h1 := Finset.card_le_card hsub
    rw [card_lt_lemma n (m.val + 1) (by omega)] at h1
    omega

theorem idxWeight_can {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) : idxWeight (canIdx μ) = μ := by
  funext m
  unfold idxWeight
  have h1 : {c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c} = Set.Icc 1 (μ m) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hc, hm⟩
      unfold canIdx at hm
      rw [if_pos hc] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact ⟨hc, (lt_colHeight_iff_lemma h c m).mp hm⟩
    · rintro ⟨hc, hcm⟩
      refine ⟨hc, ?_⟩
      unfold canIdx
      rw [if_pos hc]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (lt_colHeight_iff_lemma h c m).mpr hcm
  have h2 : {c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c} = Set.Ioc (μ m) 0 := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨hc, hm⟩
      unfold canIdx at hm
      rw [if_neg (show ¬ (1 ≤ c) by omega)] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have h3 : ¬ c ≤ μ m := fun h' => absurd ((lt_colHeight_iff_lemma h c m).mpr h') (by omega)
      exact ⟨by omega, hc⟩
    · rintro ⟨hlt, hc⟩
      refine ⟨hc, ?_⟩
      unfold canIdx
      rw [if_neg (show ¬ (1 ≤ c) by omega)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hlt2
      have := (lt_colHeight_iff_lemma h c m).mp (by omega)
      omega
  rw [h1, h2, ← Finset.coe_Icc, ← Finset.coe_Ioc, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Int.card_Icc, Int.card_Ioc]
  omega

def rowsLt (n j : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < j

private theorem card_rowsLt_lemma (n k : ℕ) : (rowsLt n k).card = min k n := by
  unfold rowsLt
  rcases le_total k n with hk | hk
  · rw [card_lt_lemma n k hk]
    omega
  · rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    · omega
    · intro m _
      have := m.isLt
      omega

theorem cnt_init {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = (rowsLt n h).card) :
    ((rowsLt n j).filter fun m => m ∈ J).card ≤ ((rowsLt n j).filter fun m => m ∈ rowsLt n h).card := by
  have e : ((rowsLt n j).filter fun m => m ∈ rowsLt n h) = rowsLt n (min j h) := by
    ext m
    simp [rowsLt, lt_min_iff]
  rw [e, card_rowsLt_lemma]
  have h1 := Finset.card_le_card (Finset.filter_subset (fun m => m ∈ J) (rowsLt n j))
  have h2 : ((rowsLt n j).filter fun m => m ∈ J).card ≤ J.card :=
    Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
  rw [card_rowsLt_lemma] at h1 hJ
  omega

theorem card_filter_lt_le_alt {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = ((rowsLt n h)ᶜ).card) :
    ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ).card ≤ ((rowsLt n j).filter fun m => m ∈ J).card := by
  have f1 : ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ) = rowsLt n j ∩ (rowsLt n h)ᶜ := by
    ext m
    simp
  have f2 : ((rowsLt n j).filter fun m => m ∈ J) = rowsLt n j ∩ J := by
    ext m
    simp
  rw [f1, f2]
  rcases le_total j h with hjh | hjh
  · have e : rowsLt n j ∩ (rowsLt n h)ᶜ = ∅ := by
      ext m
      constructor
      · intro hm
        simp only [rowsLt, Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
          true_and] at hm
        exact absurd hm (by omega)
      · intro hm
        simp at hm
    rw [e, Finset.card_empty]
    exact Nat.zero_le _
  · have hu : rowsLt n j ∪ (rowsLt n h)ᶜ = univ := by
      ext m
      simp only [rowsLt, Finset.mem_union, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      omega
    have e1 := Finset.card_union_add_card_inter (rowsLt n j) ((rowsLt n h)ᶜ)
    have e2 := Finset.card_union_add_card_inter (rowsLt n j) J
    have e3 := Finset.card_le_univ (rowsLt n j ∪ J)
    rw [hu, Finset.card_univ, Fintype.card_fin] at e1
    rw [Fintype.card_fin] at e3
    omega

theorem can_pos {n : ℕ} (μ : Fin n → ℤ) {c : ℤ} (hc : 1 ≤ c) :
    canIdx μ c = rowsLt n (colHeight μ c) := by
  unfold canIdx rowsLt
  rw [if_pos hc]

theorem can_neg {n : ℕ} (μ : Fin n → ℤ) {c : ℤ} (hc : ¬ 1 ≤ c) :
    canIdx μ c = (rowsLt n (colHeight μ c))ᶜ := by
  unfold canIdx rowsLt
  rw [if_neg hc]
  ext m
  simp

theorem col_le {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ) (j : ℕ) :
    (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ I c).card : ℤ) ≤
      (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
  have hle : colHeight μ c ≤ n := by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have key := hI c
  by_cases hc : 1 ≤ c
  · rw [if_pos hc] at key ⊢
    rw [can_pos μ hc]
    have := cnt_init (I c) (colHeight μ c) j (by rw [key, card_rowsLt_lemma]; omega)
    simp only [one_mul]
    exact_mod_cast this
  · rw [if_neg hc] at key ⊢
    rw [can_neg μ hc]
    have := card_filter_lt_le_alt (I c) (colHeight μ c) j
      (by rw [key, Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma]; omega)
    have h' : (((rowsLt n j).filter fun m => m ∈ (rowsLt n (colHeight μ c))ᶜ).card : ℤ) ≤
        (((rowsLt n j).filter fun m => m ∈ I c).card : ℤ) := by
      exact_mod_cast this
    linarith

theorem col_eq {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ)
    (h : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card =
      ((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card) : I c = canIdx μ c := by
  have hle : colHeight μ c ≤ n := by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have key := hI c
  by_cases hc : 1 ≤ c
  · rw [if_pos hc] at key
    rw [can_pos μ hc] at h ⊢
    have f1 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ I c :=
      fun x hx => (Finset.mem_filter.mp hx).2
    have f2 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ rowsLt n (colHeight μ c) :=
      Finset.filter_subset _ _
    have e : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ rowsLt n (colHeight μ c)) =
        rowsLt n (colHeight μ c) :=
      Finset.filter_true_of_mem fun x hx => hx
    rw [e, card_rowsLt_lemma] at h
    have g1 := Finset.eq_of_subset_of_card_le f1 (by omega)
    have g2 := Finset.eq_of_subset_of_card_le f2 (by rw [card_rowsLt_lemma]; omega)
    exact g1.symm.trans g2
  · rw [if_neg hc] at key
    rw [can_neg μ hc] at h ⊢
    have e : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ (rowsLt n (colHeight μ c))ᶜ) = ∅ := by
      ext m
      simp
    rw [e, Finset.card_empty] at h
    have hsub : I c ⊆ (rowsLt n (colHeight μ c))ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxR
      have hmem : x ∈ (rowsLt n (colHeight μ c)).filter fun m => m ∈ I c :=
        Finset.mem_filter.mpr ⟨hxR, hx⟩
      rw [Finset.card_eq_zero.mp h] at hmem
      simp at hmem
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma, key]; omega)

end A3comb

open A3comb in
theorem index_weights_dominance : IndexWeightsDominance := by
  intro n μ I hμ hI
  obtain ⟨M, hM⟩ := exists_bound μ
  have hS : ∀ c, c ∉ Finset.Icc (-M) M → I c = ∅ := fun c hc => idx_empty hI M hM c hc
  have hle : ∀ c, colHeight μ c ≤ n := fun c => by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hcan : IsIndex μ (canIdx μ) := by
    intro c
    have := hle c
    by_cases hc : 1 ≤ c
    · rw [if_pos hc, can_pos μ hc, card_rowsLt_lemma]
      omega
    · rw [if_neg hc, can_neg μ hc, Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma]
      omega
  have hS' : ∀ c, c ∉ Finset.Icc (-M) M → canIdx μ c = ∅ := fun c hc => idx_empty hcan M hM c hc
  have hsum : ∀ j, ∑ m ∈ rowsLt n j, idxWeight I m ≤ ∑ m ∈ rowsLt n j, μ m := by
    intro j
    rw [show (∑ m ∈ rowsLt n j, μ m) = ∑ m ∈ rowsLt n j, idxWeight (canIdx μ) m by
      rw [idxWeight_can hμ], sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    exact Finset.sum_le_sum fun c _ => col_le hI c j
  have e : (Finset.univ : Finset (Fin n)) = rowsLt n n := by
    ext m
    simp [rowsLt]
  have g : ∀ X : Finset (Fin n), ((rowsLt n n).filter fun m => m ∈ X) = X := by
    intro X
    rw [← e]
    ext m
    simp
  have htot : ∑ m, idxWeight I m = ∑ m, μ m := by
    rw [e, show (∑ m ∈ rowsLt n n, μ m) = ∑ m ∈ rowsLt n n, idxWeight (canIdx μ) m by
      rw [idxWeight_can hμ], sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [g, g, hI c, hcan c]
  refine ⟨?_, fun hw => ?_⟩
  · unfold DomLe
    exact ⟨htot, fun j => hsum j⟩
  funext c
  by_cases hcS : c ∈ Finset.Icc (-M) M
  · apply col_eq hI c
    have hsum0 : ∑ c' ∈ Finset.Icc (-M) M, ((if 1 ≤ c' then (1 : ℤ) else -1) *
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c').card : ℤ) -
        (if 1 ≤ c' then (1 : ℤ) else -1) *
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c').card : ℤ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← sum_idxWeight I _ hS, ← sum_idxWeight (canIdx μ) _ hS',
        idxWeight_can hμ, hw, sub_self]
    rw [Finset.sum_eq_zero_iff_of_nonpos
      (fun c' _ => sub_nonpos.mpr (col_le hI c' (colHeight μ c)))] at hsum0
    have h0 := hsum0 c hcS
    have h1 : (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card : ℤ) =
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
      split_ifs at h0 <;> linarith
    exact_mod_cast h1
  · rw [hS c hcS, hS' c hcS]

namespace A3comb

theorem weight_letter {n : ℕ} (i : ℕ) (e : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) e = ∑ a, e (i, a) := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, hf, hg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  · rintro ⟨x1, x2⟩ k
    rw [Finsupp.weight_apply, Finsupp.sum_single_index]
    · by_cases hi : x1 = i
      · subst hi
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, hi]
    · simp

def mkMon {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) : ℕ × Fin n →₀ ℕ :=
  Finsupp.onFinset (range N ×ˢ univ) (fun x => if h : x.1 < N then d ⟨x.1, h⟩ x.2 else 0) (by
    intro x hx
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, Finset.mem_univ _⟩
    by_contra h
    exact hx (dif_neg h))

theorem mkMon_apply {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) (i : Fin N) (a : Fin n) :
    mkMon d (i.val, a) = d i a := by
  simp [mkMon]

theorem mkMon_apply_ge {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) (i : ℕ) (hi : ¬ i < N) (a : Fin n) :
    mkMon d (i, a) = 0 := by
  simp [mkMon, hi]

theorem mkMon_inj {n N : ℕ} : Function.Injective (mkMon (n := n) (N := N)) := by
  intro d d' h
  funext i
  ext a
  have := DFunLike.congr_fun h (i.val, a)
  rwa [mkMon_apply, mkMon_apply] at this

theorem monSet_eq (n N : ℕ) (B : ℕ → ℕ) :
    {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0} =
      ↑((Fintype.piFinset fun i : Fin N => (univ : Finset (Fin n)).finsuppAntidiag (B i)).image
        mkMon) := by
  ext e
  simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Fintype.mem_piFinset, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  constructor
  · intro he
    refine ⟨fun i => Finsupp.equivFunOnFinite.symm fun a => e (i.val, a), fun i => ?_, ?_⟩
    · simpa using he i.val
    · ext ⟨j, a⟩
      by_cases hj : j < N
      · exact (mkMon_apply _ ⟨j, hj⟩ a).trans (by simp)
      · rw [mkMon_apply_ge _ _ hj]
        have := he j
        rw [if_neg hj, Finset.sum_eq_zero_iff] at this
        exact (this a (Finset.mem_univ a)).symm
  · rintro ⟨d, hd, rfl⟩ i
    by_cases hi : i < N
    · rw [if_pos hi]
      exact (Finset.sum_congr rfl fun a _ => mkMon_apply d ⟨i, hi⟩ a).trans (hd ⟨i, hi⟩)
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun a _ => mkMon_apply_ge d i hi a

end A3comb

open A3comb in
theorem polynomial_b_rank : PolBRank := by
  intro n N B
  have hcard : ∀ k : ℕ, ((univ : Finset (Fin n)).finsuppAntidiag k).card = (n + k - 1).choose k := by
    intro k
    rw [show n + k - 1 = Fintype.card (Fin n) + k - 1 by simp, ← Sym.card_sym_eq_choose,
      ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv
      ({ toFun := fun f => Finsupp.toMultiset f, invFun := fun s => Multiset.toFinsupp s,
         left_inv := fun f => by simp, right_inv := fun s => by simp } : (Fin n →₀ ℕ) ≃ Multiset (Fin n))
      (fun f => by
      simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Equiv.coe_fn_mk,
        Finsupp.card_toMultiset]
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      rfl) : _ ≃ Sym (Fin n) k)
  have hset := monSet_eq n N B
  refine ⟨?_, ?_, ?_⟩
  · rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ mkMon_inj,
      Fintype.card_piFinset,
      Fin.prod_univ_eq_prod_range (fun i => ((univ : Finset (Fin n)).finsuppAntidiag (B i)).card) N]
    exact Finset.prod_congr rfl fun i _ => hcard (B i)
  · rw [hset]
    exact Finset.finite_toSet _
  · intro R _
    apply le_antisymm
    · intro p hp
      unfold polB at hp
      rw [Submodule.mem_iInf] at hp
      rw [p.as_sum]
      refine Submodule.sum_mem _ fun e he => ?_
      have heS : ∀ i, ∑ a, e (i, a) = if i < N then B i else 0 := by
        intro i
        rw [← weight_letter]
        exact ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hp i))
          (MvPolynomial.mem_support_iff.mp he)
      rw [show MvPolynomial.monomial e (MvPolynomial.coeff e p) =
          MvPolynomial.coeff e p • MvPolynomial.monomial e (1 : R) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_image_of_mem (fun e => MvPolynomial.monomial e (1 : R)) heS))
    · rw [Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have he' : ∀ i, ∑ a, e (i, a) = if i < N then B i else 0 := he
      unfold polB
      rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro i
      rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [weight_letter]
      exact he' i

namespace A3comb

theorem strip_bound {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (m : Fin n) :
    μ m ≤ ν m ∧ ν m ≤ μ m + b := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨h1 m, ?_⟩
  have : ν m - μ m ≤ ∑ m', (ν m' - μ m') :=
    Finset.single_le_sum (f := fun m' => ν m' - μ m') (fun i _ => sub_nonneg.mpr (h1 i))
      (Finset.mem_univ m)
  rw [Finset.sum_sub_distrib, h3] at this
  linarith

theorem path_bound {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) : ∀ i ≤ N, ∀ m, |μ i m| ≤ ((∑ k ∈ range i, B k : ℕ) : ℤ) := by
  obtain ⟨h0, _, hstep⟩ := hp
  intro i
  induction i with
  | zero =>
    intro _ m
    simp [h0]
  | succ i ih =>
    intro hi m
    have ih' := ih (by omega) m
    have hs := hstep i (by omega)
    rw [Finset.sum_range_succ, Nat.cast_add]
    split_ifs at hs with hv
    · have := strip_bound hs m
      rw [abs_le] at ih' ⊢
      constructor <;> linarith [this.1, this.2]
    · have := strip_bound hs m
      rw [abs_le] at ih' ⊢
      constructor <;> linarith [this.1, this.2]

theorem path_bound' {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (i : ℕ) (hi : i ≤ N) (m : Fin n) :
    |μ i m| ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
  have := path_bound hp i hi m
  have h2 : (∑ k ∈ range i, B k) ≤ ∑ k ∈ range N, B k :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hi)
  have h3 : ((∑ k ∈ range i, B k : ℕ) : ℤ) ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
    exact_mod_cast h2
  linarith

end A3comb

open A3comb in
theorem path_index_finite : PathIdxFinite := by
  intro n N isVec B
  have hb : ∀ x : PathIdx n N isVec B, ∀ i : Fin (N + 1), ∀ m,
      x.1.1 i m ∈ Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
    intro x i m
    rw [Finset.mem_Icc, ← abs_le]
    exact path_bound' x.2.1 i.val (Nat.lt_succ_iff.mp i.isLt) m
  refine Finite.of_injective
    (fun x : PathIdx n N isVec B =>
      ((fun (i : Fin (N + 1)) (m : Fin n) => (⟨x.1.1 i m, hb x i m⟩ :
          Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ))),
        fun c : Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ) =>
          x.1.2 c.1)) ?_
  rintro ⟨⟨μ, I⟩, hp, hz, hstd⟩ ⟨⟨μ', I'⟩, hp', hz', hstd'⟩ h
  dsimp only at hp hz hstd hp' hz' hstd' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hμ : μ = μ' := by
    funext i m
    by_cases hi : i ≤ N
    · have := congrArg Subtype.val (congrFun (congrFun h1 ⟨i, Nat.lt_succ_of_le hi⟩) m)
      simpa using this
    · rw [hz i (by omega), hz' i (by omega)]
  have hI : I = I' := by
    funext c
    by_cases hc : c ∈ Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ)
    · exact congrFun h2 ⟨c, hc⟩
    · rw [idx_empty hstd.1 _ (fun m => path_bound' hp N le_rfl m) c hc,
        idx_empty hstd'.1 _ (fun m => path_bound' hp' N le_rfl m) c hc]
  subst hμ hI
  rfl

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
