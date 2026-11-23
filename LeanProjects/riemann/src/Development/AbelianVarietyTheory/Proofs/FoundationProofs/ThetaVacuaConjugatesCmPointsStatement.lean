import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacua_conjugates_cmPoints : ∀ D : D7, useConj D := by
  first | exact @GlobalTheory.ThetaConj.useConj_all | exact GlobalTheory.ThetaConj.useConj_all | (intros; apply GlobalTheory.ThetaConj.useConj_all <;> assumption)
