import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_rational_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRat := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | exact GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | (intros; apply GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat <;> assumption)
