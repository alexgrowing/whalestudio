import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaussianOddJacobiThetaEqDerivMulSgStar
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar : Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  first | exact @GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | exact GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | (intros; apply GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar <;> assumption)
