import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_characters_exist : ∀ D : D7, GaussSumTripleConstant D := by
  first | exact @GlobalTheory.TripleIntertwiner.triple_constant | exact GlobalTheory.TripleIntertwiner.triple_constant | (intros; apply GlobalTheory.TripleIntertwiner.triple_constant <;> assumption)
