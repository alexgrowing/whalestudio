import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ExtendsToFractionField
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem extend_to_fraction_field_relay : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ :=
  PositivityTheory.UnitarySelfGeneration.extends_to_fraction_field

end GlobalTheory.CompanionTheory.Ggeo
