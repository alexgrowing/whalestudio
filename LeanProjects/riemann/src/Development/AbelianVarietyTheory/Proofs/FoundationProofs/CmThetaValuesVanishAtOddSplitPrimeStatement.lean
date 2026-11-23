import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime : ∀ D : D7, GL3Theta.splitZero D := by
  first | exact @GlobalTheory.ThetaSplit.splitZero | exact GlobalTheory.ThetaSplit.splitZero | (intros; apply GlobalTheory.ThetaSplit.splitZero <;> assumption)
