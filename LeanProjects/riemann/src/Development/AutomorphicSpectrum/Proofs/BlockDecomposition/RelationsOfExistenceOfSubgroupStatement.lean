import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationsOfExistenceOfSubgroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relations_of_existence_of_subgroup : ExSub → RelOfMain := by
  first | exact @GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub | exact GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub | (intros; apply GlobalTheory.CompanionTheory.LocalParam.relOfMain_of_exSub <;> assumption)
