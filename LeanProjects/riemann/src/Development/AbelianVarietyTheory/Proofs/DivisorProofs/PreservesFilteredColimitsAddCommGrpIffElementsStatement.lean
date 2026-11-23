import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElements
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ T) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, N.map (c.ι.app j) y = x) ∧ ∀ j (y : N.obj (D.obj j)), N.map (c.ι.app j) y = 0 → ∃ (k : J) (f : j ⟶ k), N.map (D.map f) y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (exact GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (intros; apply GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements  <;> assumption)
