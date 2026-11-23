import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseFieldGeneratorLocalDifferentInertPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  first | exact @GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | exact GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | (intros; apply GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt <;> assumption)
