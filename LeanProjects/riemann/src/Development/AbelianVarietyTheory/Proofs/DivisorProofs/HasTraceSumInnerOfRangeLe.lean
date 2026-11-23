import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

namespace GlobalTheory.OpTrace

theorem hasTrace_sum_inner_of_range_le (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (T : U →L[ℂ] U)
    (hT : ∀ u, T u ∈ L) :
    HasTrace T (∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U)
      (T (stdOrthonormalBasis ℂ L j : U))) := by
  have hle : LinearMap.range (T : U →ₗ[ℂ] U) ≤ L := by
    rintro _ ⟨x, rfl⟩; exact hT x
  have := Submodule.finiteDimensional_of_le hle
  have h := hasTrace_of_finiteRank T
  rw [finRankTrace_eq (T : U →ₗ[ℂ] U) L hT,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ L)] at h
  exact h

end GlobalTheory.OpTrace
