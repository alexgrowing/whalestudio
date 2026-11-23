import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclidean
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_total_of_euclidean : EucTotal → FockTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | exact GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal <;> assumption)
