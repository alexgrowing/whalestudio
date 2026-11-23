import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_trees : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | exact GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | (intros; apply GlobalTheory.CompanionTheory.EGlue.LimT.limTrees <;> assumption)
