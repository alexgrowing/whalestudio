import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceOfSubgroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_subgroup : ExSub := by
  first | exact @GlobalTheory.CompanionTheory.ExSubLeaf.exSub | exact GlobalTheory.CompanionTheory.ExSubLeaf.exSub | (intros; apply GlobalTheory.CompanionTheory.ExSubLeaf.exSub <;> assumption)
