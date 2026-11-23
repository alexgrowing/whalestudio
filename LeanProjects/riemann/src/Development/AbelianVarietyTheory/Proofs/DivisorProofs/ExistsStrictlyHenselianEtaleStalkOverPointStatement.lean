import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom → ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S) (g : Over.mk s ⟶ U), IsStalk O s ∧ ∃ v, g.left v = u := by
  first | (exact @GlobalTheory.EtC.exists_isStalk_over_point) | (exact GlobalTheory.EtC.exists_isStalk_over_point) | (intros; apply GlobalTheory.EtC.exists_isStalk_over_point  <;> assumption)
