import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceComposition
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_composition : GlobalTheory.CompanionTheory.EGlue.ConvComp := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convComp_proved | exact GlobalTheory.CompanionTheory.EGlue.convComp_proved | (intros; apply GlobalTheory.CompanionTheory.EGlue.convComp_proved <;> assumption)
