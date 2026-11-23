import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

open Polynomial

namespace GlobalTheory

theorem exists_galois_subfield_conj_stable (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ (∀ z ∈ S, z ∈ K) ∧
      Complex.I ∈ K ∧ ∀ z ∈ K, starRingEnd ℂ z ∈ K := by
  classical
  have hI : IsIntegral ℚ Complex.I := by
    refine ⟨X ^ 2 + C 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [Complex.I_sq]
  have hint : ∀ z ∈ insert Complex.I S, IsIntegral ℚ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hI
    · exact (hS z hz).isIntegral
  obtain ⟨p, hp⟩ : ∃ p : ℚ[X], p = ∏ z ∈ insert Complex.I S, minpoly ℚ z := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact Finset.prod_ne_zero_iff.2 fun z hz => minpoly.ne_zero (hint z hz)
  have hroot : ∀ z ∈ insert Complex.I S, z ∈ p.rootSet ℂ := by
    intro z hz
    rw [mem_rootSet]
    refine ⟨hp0, ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (minpoly ℚ) hz
    rw [hp, hq, map_mul, minpoly.aeval, zero_mul]
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have : p.IsSplittingField ℚ K :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
  have hfin : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K p
  have : Normal ℚ K := Normal.of_isSplittingField p
  refine ⟨K, hfin, IsGalois.mk,
    fun z hz => IntermediateField.subset_adjoin ℚ _ (hroot z (Finset.mem_insert_of_mem hz)),
    IntermediateField.subset_adjoin ℚ _ (hroot _ (Finset.mem_insert_self _ _)), ?_⟩
  let φ : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have hsub : φ '' (p.rootSet ℂ) ⊆ p.rootSet ℂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_rootSet] at hw ⊢
    exact ⟨hw.1, by rw [Polynomial.aeval_algHom_apply, hw.2, map_zero]⟩
  have hle : K.map φ ≤ K := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  intro z hz
  exact hle ⟨z, hz, rfl⟩

end GlobalTheory
