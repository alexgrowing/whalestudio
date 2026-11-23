import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_lists : GlobalTheory.CompanionTheory.EGlue.ConvStrip → GlobalTheory.CompanionTheory.EGlue.ConvShift → GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimLists := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.limLists | exact GlobalTheory.CompanionTheory.EGlue.limLists | (intros; apply GlobalTheory.CompanionTheory.EGlue.limLists <;> assumption)
