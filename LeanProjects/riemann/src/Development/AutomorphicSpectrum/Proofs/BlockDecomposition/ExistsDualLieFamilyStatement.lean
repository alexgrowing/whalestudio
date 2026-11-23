import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_lie_family : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | exact GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | (intros; apply GlobalTheory.CompanionTheory.RealCountG.dualFam_exists <;> assumption)
