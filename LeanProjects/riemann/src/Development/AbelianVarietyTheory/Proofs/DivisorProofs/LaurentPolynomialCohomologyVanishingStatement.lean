import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_locally_acyclic : GlobalTheory.EtC.C5 := by
  first | (exact @GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (exact GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (intros; apply GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing  <;> assumption)
