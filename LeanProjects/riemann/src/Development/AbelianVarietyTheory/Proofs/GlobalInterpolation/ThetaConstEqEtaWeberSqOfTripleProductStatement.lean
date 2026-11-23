import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaConstEqEtaWeberSqOfTripleProduct
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ := by
  first | exact @GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | exact GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | (intros; apply GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct <;> assumption)
