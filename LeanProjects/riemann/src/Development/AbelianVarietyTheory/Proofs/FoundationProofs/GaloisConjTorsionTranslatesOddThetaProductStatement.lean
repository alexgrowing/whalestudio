import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTorsionTranslatesOddThetaProduct
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct : ∀ D : D7, galB D := by
  first | exact @GlobalTheory.ProdThetaConj.galB_all | exact GlobalTheory.ProdThetaConj.galB_all | (intros; apply GlobalTheory.ProdThetaConj.galB_all <;> assumption)
