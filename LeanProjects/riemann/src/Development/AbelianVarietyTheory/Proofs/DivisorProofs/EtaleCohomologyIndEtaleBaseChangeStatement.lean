import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_ind_etale_base_change : GlobalTheory.EtC.C3 := by
  first | (exact @GlobalTheory.EtC.LineAcyc.c3) | (exact GlobalTheory.EtC.LineAcyc.c3) | (intros; apply GlobalTheory.EtC.LineAcyc.c3  <;> assumption)
