import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_point_dictionary : GlobalTheory.CompanionTheory.MixZ.PtDict := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ptDict | exact GlobalTheory.CompanionTheory.MixZ.ptDict | (intros; apply GlobalTheory.CompanionTheory.MixZ.ptDict <;> assumption)
