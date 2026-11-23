import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_etaleCohomologyEquivalence_diagram : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt), (∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) → (∀ i, Eqv R (α.app i) F) → Eqv R β F → (ContCone R F c ↔ ContCone R F c') := by
  first | (exact @GlobalTheory.EtC.ContCone.iff_of_eqv) | (exact GlobalTheory.EtC.ContCone.iff_of_eqv) | (intros; apply GlobalTheory.EtC.ContCone.iff_of_eqv  <;> assumption)
