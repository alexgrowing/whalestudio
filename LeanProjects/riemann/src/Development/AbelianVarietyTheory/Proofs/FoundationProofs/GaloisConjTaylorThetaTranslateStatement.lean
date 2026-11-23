import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_taylor_thetaTranslate : ∀ D : D7, gal1 D := by
  first | exact @GlobalTheory.JetConj.galois_translate_sgStar | exact GlobalTheory.JetConj.galois_translate_sgStar | (intros; apply GlobalTheory.JetConj.galois_translate_sgStar <;> assumption)
