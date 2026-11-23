import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

def LiftAt {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀

def LiftIn {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) (V : X.left.Opens) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤

end GlobalTheory.SecLift
