import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_second_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₂ := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairStep₂ | exact GlobalTheory.CompanionTheory.EGlue.pairStep₂ | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairStep₂ <;> assumption)
