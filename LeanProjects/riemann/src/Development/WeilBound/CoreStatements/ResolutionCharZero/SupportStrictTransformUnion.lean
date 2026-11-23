import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open FunctorialResolution

def GTransform : Prop :=
  ∀ (X X₁ : Scheme.{0}) (π : X₁ ⟶ X) (Z D : X.IdealSheafData), IsLocallyNoetherian X → IsLocallyNoetherian X₁ →
    IsBlowup π Z →
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X)

theorem strictTransform_eq_blowup {X X₁ : Scheme.{0}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransform π Z D = Blowup.strictTransform π Z D := rfl

theorem support_strictTransform_union {X X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X) := by
  rw [strictTransform_eq_blowup]
  apply Set.Subset.antisymm
  · refine Set.union_subset_union_left _ ?_
    exact EmbeddedResolution.support_strictTransform_subset_preimage π Z D
  · rintro x (hx | hx)
    · by_cases hz : π.base x ∈ (Z.support : Set X)
      · exact Or.inr hz
      · exact Or.inl ((EmbeddedResolution.mem_support_strictTransform_iff_of_notMem_support π Z D x hz).2 hx)
    · exact Or.inr hx

theorem gTransform : GTransform := fun _ _ π Z D _ _ _ => support_strictTransform_union π Z D

end PositivityTheory.ResPlug.WeightsCompactStabilizer
