import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  first | exact @GlobalTheory.Phase.ph_haar_of_shape | exact GlobalTheory.Phase.ph_haar_of_shape | (intros; apply GlobalTheory.Phase.ph_haar_of_shape <;> assumption)
