import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_read_combination : GlobalTheory.CompanionTheory.MixZ.ReadComb := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.readComb | exact GlobalTheory.CompanionTheory.MixZ.readComb | (intros; apply GlobalTheory.CompanionTheory.MixZ.readComb <;> assumption)
