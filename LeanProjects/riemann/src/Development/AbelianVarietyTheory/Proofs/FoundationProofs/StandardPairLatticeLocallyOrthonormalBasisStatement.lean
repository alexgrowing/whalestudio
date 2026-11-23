import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairLattice_locally_orthonormal_basis : ∀ D : D7, odd1 D := by
  first | exact @GlobalTheory.OddGenus.odd_one | exact GlobalTheory.OddGenus.odd_one | (intros; apply GlobalTheory.OddGenus.odd_one <;> assumption)
