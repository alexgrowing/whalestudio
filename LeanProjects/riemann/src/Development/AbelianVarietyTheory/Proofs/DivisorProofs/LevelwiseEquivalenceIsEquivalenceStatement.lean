import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
