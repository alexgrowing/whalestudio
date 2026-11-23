import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlip
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_graded_comm_of_isFlip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  first | exact @GlobalTheory.EtC.Pair.cup_flip | exact GlobalTheory.EtC.Pair.cup_flip | (intros; apply GlobalTheory.EtC.Pair.cup_flip <;> assumption)
