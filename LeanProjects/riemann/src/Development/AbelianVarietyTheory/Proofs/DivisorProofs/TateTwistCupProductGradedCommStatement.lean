import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedComm
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_graded_comm : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.cup_comm
  | exact GlobalTheory.EtC.cup_comm
  | (intros; apply GlobalTheory.EtC.cup_comm <;> assumption)
