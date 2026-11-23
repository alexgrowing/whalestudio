import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity : GlobalTheory.EtC.B1 := by
  first | (exact @GlobalTheory.EtC.pairingProperties) | (exact GlobalTheory.EtC.pairingProperties) | (intros; apply GlobalTheory.EtC.pairingProperties  <;> assumption)
