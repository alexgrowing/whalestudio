import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_log_orthogonal_weight_constant : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ), (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) → (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) → ∀ sg sg', m sg = m sg' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units | exact GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units <;> assumption)
