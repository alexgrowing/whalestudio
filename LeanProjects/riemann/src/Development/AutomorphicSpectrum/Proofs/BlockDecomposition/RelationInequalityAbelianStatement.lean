import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationInequalityAbelian
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relation_inequality_abelian : RelIneAb := by
  first | exact @GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | exact GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | (intros; apply GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb <;> assumption)
