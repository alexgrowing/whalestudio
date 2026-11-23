import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselian
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
