import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

namespace ExtNonInt

theorem det_restrictScalars_complex {D : ℕ} (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) :
    (L.restrictScalars ℝ).det = ‖LinearMap.det (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 := by
  change LinearMap.det ((L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)).restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

variable {D : ℕ} {U : Type} [TopologicalSpace U]

end ExtNonInt

end

end GroundTheory.Heights₂.Heights.EffectiveHS
