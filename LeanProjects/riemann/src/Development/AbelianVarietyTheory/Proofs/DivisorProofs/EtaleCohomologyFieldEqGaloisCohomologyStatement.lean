import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomology
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology : GlobalTheory.EtC.B7 := by
  first | (exact @GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (exact GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (intros; apply GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois  <;> assumption)
