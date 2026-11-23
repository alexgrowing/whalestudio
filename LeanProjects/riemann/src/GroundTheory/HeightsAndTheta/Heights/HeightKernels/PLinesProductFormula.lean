import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesProductFormula

theorem prod_norm_embeddings (K : Type) [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have h := congr_arg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
    (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [← h, eq_ratCast, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

end KLinesProductFormula

theorem LinesProductFormula.proof : LinesProductFormula.Statement := by
  intro K _ _ x hx
  rw [← KLinesProductFormula.prod_norm_embeddings K x, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

end GroundTheory.Heights₂.Heights
