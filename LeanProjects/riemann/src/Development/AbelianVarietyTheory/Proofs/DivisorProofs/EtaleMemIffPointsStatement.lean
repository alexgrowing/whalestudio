import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etale_covering_sieves_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔ ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  first | (exact @GlobalTheory.etale_mem_iff_points) | (exact GlobalTheory.etale_mem_iff_points) | (intros; apply GlobalTheory.etale_mem_iff_points  <;> assumption)
