import Mathlib

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩

theorem isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk

end ReciprocityTheory.Cheb
