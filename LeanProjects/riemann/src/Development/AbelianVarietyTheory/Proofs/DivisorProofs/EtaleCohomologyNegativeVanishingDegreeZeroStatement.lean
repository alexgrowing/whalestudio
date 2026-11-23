import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero : GlobalTheory.EtC.A9 := by
  first | exact @GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | exact GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | (intros; apply GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero <;> assumption)
