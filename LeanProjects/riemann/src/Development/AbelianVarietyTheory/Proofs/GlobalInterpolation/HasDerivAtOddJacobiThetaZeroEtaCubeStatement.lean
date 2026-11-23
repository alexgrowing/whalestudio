import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCube
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  first | exact @GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | exact GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | (intros; apply GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero <;> assumption)
