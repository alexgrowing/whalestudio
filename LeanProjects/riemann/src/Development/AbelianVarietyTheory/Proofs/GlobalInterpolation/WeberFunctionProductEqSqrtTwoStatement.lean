import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwo
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberFunction_product_eq_sqrt_two : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ) := by
  first | exact @GlobalTheory.WeberProduct.weber_prod | exact GlobalTheory.WeberProduct.weber_prod | (intros; apply GlobalTheory.WeberProduct.weber_prod <;> assumption)
