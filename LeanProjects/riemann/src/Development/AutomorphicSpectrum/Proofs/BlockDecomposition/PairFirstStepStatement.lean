import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStep
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_first_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices | exact GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices | (intros; apply GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices <;> assumption)
