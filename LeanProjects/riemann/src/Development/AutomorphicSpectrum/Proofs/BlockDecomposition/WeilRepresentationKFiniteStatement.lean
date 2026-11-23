import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_K_finite : WeilKFin := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilKFin | exact GlobalTheory.CompanionTheory.ThTot.weilKFin | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilKFin <;> assumption)
