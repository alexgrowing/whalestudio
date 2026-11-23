import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
