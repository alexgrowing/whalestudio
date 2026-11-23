import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem hom_ext_of_localRing_points :
    ∀ (X Y : Scheme.{0}) (f g : X ⟶ Y),
      (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ X), t ≫ f = t ≫ g) → f = g :=
  fun X _ _ _ h => hom_ext_of_fromSpecStalk fun x =>
    @h (X.presheaf.stalk x) _ (X.toLocallyRingedSpace.isLocalRing x) (X.fromSpecStalk x)

end GlobalTheory
