import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdClose
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_facts_alt : GlobalTheory.CompanionTheory.EGlue.MCloseFacts := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | exact GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds <;> assumption)
