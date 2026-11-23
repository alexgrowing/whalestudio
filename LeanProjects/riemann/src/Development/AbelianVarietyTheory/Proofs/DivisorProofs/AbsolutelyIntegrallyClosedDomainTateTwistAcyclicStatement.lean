import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic : GlobalTheory.EtC.B5 := by
  first | (exact @GlobalTheory.EtC.b5) | (exact GlobalTheory.EtC.b5) | (intros; apply GlobalTheory.EtC.b5  <;> assumption)
