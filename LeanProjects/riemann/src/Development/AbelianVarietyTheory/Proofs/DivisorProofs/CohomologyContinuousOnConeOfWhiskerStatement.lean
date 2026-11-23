import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousOnConeOfWhisker
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuousOnCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  first | (exact @GlobalTheory.EtC.contCone_of_whisker) | (exact GlobalTheory.EtC.contCone_of_whisker) | (intros; apply GlobalTheory.EtC.contCone_of_whisker  <;> assumption)
