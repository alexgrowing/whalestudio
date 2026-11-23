import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf : GlobalTheory.EtC.B2 := by
  first | (exact @GlobalTheory.EtC.b2) | (exact GlobalTheory.EtC.b2) | (intros; apply GlobalTheory.EtC.b2  <;> assumption)
