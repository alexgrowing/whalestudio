import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  first | exact @GlobalTheory.KapVal.norm_kappa_sq_mul_det | exact GlobalTheory.KapVal.norm_kappa_sq_mul_det | (intros; apply GlobalTheory.KapVal.norm_kappa_sq_mul_det <;> assumption)
