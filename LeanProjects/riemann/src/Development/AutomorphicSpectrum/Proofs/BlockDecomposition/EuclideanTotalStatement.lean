import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euclidean_total : EucTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | exact GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal <;> assumption)
