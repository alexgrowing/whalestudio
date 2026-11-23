import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultiple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (exact GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral  <;> assumption)
