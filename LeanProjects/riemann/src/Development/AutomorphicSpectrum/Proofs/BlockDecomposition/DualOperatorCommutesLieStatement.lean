import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_operator_commutes_lie : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | exact GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | (intros; apply GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G <;> assumption)
