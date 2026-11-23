import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import GroundTheory.PAdicHodge.SlopeCauchyBinet
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {R : Type} [CommRing R] {N : ℕ}

theorem minorIJ_eq_det (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) : minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dif_pos hI]

theorem minorIJ_of_card_ne (h : Matrix (Fin N) (Fin N) R) {I J : Finset (Fin N)} (e : I.card ≠ J.card) :
    minorIJ h I J = 0 := by
  unfold minorIJ
  rw [dif_neg e]

theorem minorIJ_mul_of_card (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) :
    minorIJ (T * h) I J = ∑ s : GroundTheory.PAdicHodge.KSubset N k, minorIJ T I s.1 * minorIJ h s.1 J := by
  rw [minorIJ_eq_det _ _ _ k hI hJ]
  have e : (T * h).submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) =
      T.submatrix (I.orderEmbOfFin hI) id * h.submatrix id (J.orderEmbOfFin hJ) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [e, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [minorIJ_eq_det T I s.1 k hI s.2, minorIJ_eq_det h s.1 J k s.2 hJ]
  rfl

theorem minorIJ_mul (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  by_cases e : I.card = J.card
  · rw [minorIJ_mul_of_card T h I J I.card rfl e.symm]
    have h1 : ∑ I' : Finset (Fin N), minorIJ T I I' * minorIJ h I' J =
        ∑ I' ∈ Finset.univ.filter (fun I' : Finset (Fin N) => I'.card = I.card),
          minorIJ T I I' * minorIJ h I' J := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
      have hc : s.card ≠ I.card := fun hc => hs (by simp [hc])
      rw [minorIJ_of_card_ne T (Ne.symm hc), zero_mul]
    rw [h1]
    exact (Finset.sum_subtype (Finset.univ.filter fun I' : Finset (Fin N) => I'.card = I.card)
      (p := fun s : Finset (Fin N) => s.card = I.card) (fun s => by simp)
      (fun I' => minorIJ T I I' * minorIJ h I' J)).symm
  · rw [minorIJ_of_card_ne _ e]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : I.card = s.card
    · rw [minorIJ_of_card_ne h (fun h' => e (hs.trans h')), mul_zero]
    · rw [minorIJ_of_card_ne T hs, zero_mul]

theorem minorIJ_eq_zero_of_row (h : Matrix (Fin N) (Fin N) R) {I C : Finset (Fin N)} {a : Fin N} (ha : a ∈ I)
    (hz : ∀ c ∈ C, h a c = 0) : minorIJ h I C = 0 := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det h I C _ e rfl]
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    simp only [Matrix.submatrix_apply]
    refine hz _ ?_
    exact Finset.orderEmbOfFin_mem _ _ _
  · exact minorIJ_of_card_ne h e

theorem sum_mem_eq_sum_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∑ k ∈ C, f k = ∑ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.sum_map]
  rfl

theorem prod_mem_eq_prod_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∏ k ∈ C, f k = ∏ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.prod_map]
  rfl

theorem minorIJ_mul_of_support (A B : Matrix (Fin N) (Fin N) R) (I C : Finset (Fin N))
    (hz : ∀ k c, c ∈ C → k ∉ C → B k c = 0) :
    minorIJ (A * B) I C = minorIJ A I C * minorIJ B C C := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det _ I C _ e rfl, minorIJ_eq_det A I C _ e rfl, minorIJ_eq_det B C C _ rfl rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    have hy : C.orderEmbOfFin rfl y ∈ C := Finset.orderEmbOfFin_mem _ _ _
    have h1 : ∑ k, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) =
        ∑ k ∈ C, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      rw [hz k _ hy hk, mul_zero]
    rw [h1, sum_mem_eq_sum_enum C]
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ e, zero_mul]

theorem minorIJ_self_of_triangular (B : Matrix (Fin N) (Fin N) R) (hB : B.BlockTriangular id) (C : Finset (Fin N)) :
    minorIJ B C C = ∏ c ∈ C, B c c := by
  rw [minorIJ_eq_det B C C _ rfl rfl]
  have ht : (B.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).BlockTriangular id := by
    intro x y hxy
    exact hB ((C.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_upperTriangular ht, prod_mem_eq_prod_enum C (fun c => B c c)]
  rfl

theorem mem_stepCols_block {N j : ℕ} {i c : Fin N} (hj : j ≤ N) (hc : c ∈ stepCols N j i) :
    if (i : ℕ) + 1 ≤ j then N - j ≤ (c : ℕ) else (c : ℕ) < N - j := by
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  split_ifs at hc ⊢ with h
  · exact hc.1
  · omega

theorem support_stepCols {N j : ℕ} {i : Fin N} (hj : j ≤ N) (bb : Matrix (Fin N) (Fin N) R)
    (hd : IsBlockDiag j bb) (ht : bb.BlockTriangular id) (k c : Fin N) (hc : c ∈ stepCols N j i)
    (hk : k ∉ stepCols N j i) : bb k c = 0 := by
  by_cases hkc : c < k
  · exact ht hkc
  have hkc' : (k : ℕ) ≤ c := by simpa using not_lt.mp hkc
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  split_ifs at hc hk with h
  · refine hd k c fun hiff => ?_
    have : ¬ (k : ℕ) < N - j → False := fun h' => hk ⟨by omega, by omega⟩
    have h3 : (k : ℕ) < N - j := by omega
    have := hiff.mp h3
    omega
  · exact absurd (by omega) hk

theorem isBlockDiag_mul {j : ℕ} {T h : Matrix (Fin N) (Fin N) R} (hT : IsBlockDiag j T) (hh : IsBlockDiag j h) :
    IsBlockDiag j (T * h) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((a : ℕ) < N - j ↔ (k : ℕ) < N - j)
  · rw [hh k b (fun h' => hab (hk.trans h')), mul_zero]
  · rw [hT a k hk, zero_mul]

theorem support_wIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ wIdx N j) (hk : k ∉ wIdx N j) : h k c = 0 := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => ?_
  have := hiff.mp (not_le.mp hk)
  omega

theorem support_omIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ omIdx N j) (hk : k ∉ omIdx N j) : h k c = 0 := by
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => hk (hiff.mpr hc)

theorem detFac_mul {j : ℕ} (i : Fin N) {T h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) :
    detFac j i (T * h) = detFac j i T * detFac j i h := by
  unfold detFac
  rw [minorIJ_mul_of_support T h _ _ (support_wIdx hh), minorIJ_mul_of_support T h _ _ (support_omIdx hh)]
  split_ifs <;> ring

theorem minor_stepCols_eq_zero {N j : ℕ} {i : Fin N} (hj : j ≤ N) (h : Matrix (Fin N) (Fin N) R)
    (I : Finset (Fin N)) (hd : IsBlockDiag j h) (hI : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  by_cases e : I.card = (stepCols N j i).card
  · have hs : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hI ⟨e, hs⟩
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    refine minorIJ_eq_zero_of_row h ha fun c hc => hd a c fun hiff => ?_
    have hb := mem_stepCols_block hj hc
    split_ifs at has hb with h1
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      have := hiff.mp (not_le.mp has)
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      exact has (hiff.mpr hb)
  · exact minorIJ_of_card_ne h e

theorem minors_main : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N →
    (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)),
      minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧
    (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I →
      minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧
    (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id →
      minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧
    ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h →
      IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  intro R _ N j i hj
  refine ⟨minorIJ_mul, fun h I hd hI => Or.inl (minor_stepCols_eq_zero hj h I hd hI), ?_, ?_⟩
  · intro h bb I hd ht
    rw [minorIJ_mul_of_support h bb I _ (support_stepCols hj bb hd ht),
      minorIJ_self_of_triangular bb ht]
  · intro T h hT hh
    exact ⟨isBlockDiag_mul hT hh, detFac_mul i hh⟩

end GlobalTheory.CompanionTheory.Ar.PB.MinorCalc
