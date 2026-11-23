import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := by
  first | (exact @GlobalTheory.EtC.tw_finitary) | (exact GlobalTheory.EtC.tw_finitary) | (intros; apply GlobalTheory.EtC.tw_finitary  <;> assumption)
