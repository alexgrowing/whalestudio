import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem appTop_injective_of_surjective_toSpec_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  intro R _ _ S π hπ hS
  rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : π ⁻¹ᵁ (Sp R).basicOpen r = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hr, Scheme.basicOpen_zero]
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ.surj x
  have hy : y ∈ π ⁻¹ᵁ (Sp R).basicOpen r := hx
  rw [h1] at hy
  exact hy.elim

end GlobalTheory
