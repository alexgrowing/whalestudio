import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models

namespace GlobalTheory.Member

theorem isDedFrac_away : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F) (x : O), β x ≠ 0 → IsDedFrac β →
    ∀ (ω : Localization.Away x →+* F), ω.comp (algebraMap O (Localization.Away x)) = β → IsDedFrac ω := by
  intro O F _ _ β x hx hβ ω hω
  obtain ⟨⟨hD, hDD⟩, hc, hfr⟩ := hβ
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (map_zero β)
  have hM : Submonoid.powers x ≤ nonZeroDivisors O := powers_le_nonZeroDivisors_of_noZeroDivisors hx0
  haveI hdom : IsDomain (Localization.Away x) := IsLocalization.isDomain_localization hM
  refine ⟨⟨hdom, IsLocalization.isDedekindDomain O hM _⟩, ?_, ?_⟩
  · exact charZero_of_injective_algebraMap (IsLocalization.injective (Localization.Away x) hM)
  · letI : Algebra O F := β.toAlgebra
    letI : Algebra (Localization.Away x) F := ω.toAlgebra
    haveI : IsScalarTower O (Localization.Away x) F := IsScalarTower.of_algebraMap_eq' hω.symm
    exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers x) _ F

end GlobalTheory.Member
