import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FinNear

theorem isAffineOpen_preimage_inf_of_isSeparated_over {Y X S : Scheme.{0}} (g : Y ⟶ X) (s : X ⟶ S)
    [IsSeparated s] {T : S.Opens} (hT : IsAffineOpen T) {D : X.Opens} (hD : IsAffineOpen D)
    (hDT : D ≤ s ⁻¹ᵁ T) {V : Y.Opens} (hV : IsAffineOpen V) (hVT : V ≤ g ⁻¹ᵁ (s ⁻¹ᵁ T)) :
    IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffine T := hT
  have : IsAffine D := hD
  let g' : V.toScheme ⟶ (s ⁻¹ᵁ T).toScheme := g.resLE (s ⁻¹ᵁ T) V hVT
  have : IsAffineHom (g' ≫ (s ∣_ T)) := isAffineHom_of_isAffine _
  have : IsAffineHom g' := IsAffineHom.of_comp g' (s ∣_ T)
  have hD' : IsAffineOpen ((s ⁻¹ᵁ T).ι ⁻¹ᵁ D) := by
    have h := isAffineOpen_opensRange (X.homOfLE hDT)
    rwa [Scheme.opensRange_homOfLE] at h
  have h := (hD'.preimage g').image_of_isOpenImmersion V.ι
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h

end GlobalTheory.FinNear

namespace GlobalTheory.FinNear

end GlobalTheory.FinNear
