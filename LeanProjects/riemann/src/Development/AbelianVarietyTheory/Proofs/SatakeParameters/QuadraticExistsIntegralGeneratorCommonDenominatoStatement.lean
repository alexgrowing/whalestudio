import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticExistsIntegralGeneratorCommonDenominato
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_generator_common_denom_of_isQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧ ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_exists_integral_generator_common_denominator | exact GlobalTheory.quadratic_exists_integral_generator_common_denominator | (intros; apply GlobalTheory.quadratic_exists_integral_generator_common_denominator <;> assumption)
