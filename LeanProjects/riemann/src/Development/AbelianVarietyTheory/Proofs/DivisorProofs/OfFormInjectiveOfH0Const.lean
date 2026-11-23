import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem ofForm_injective_of_H0Const (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r

end GlobalTheory.AbCoh
