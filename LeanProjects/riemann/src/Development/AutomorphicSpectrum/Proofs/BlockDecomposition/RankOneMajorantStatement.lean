import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_majorant : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | exact GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | (intros; apply GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts <;> assumption)
