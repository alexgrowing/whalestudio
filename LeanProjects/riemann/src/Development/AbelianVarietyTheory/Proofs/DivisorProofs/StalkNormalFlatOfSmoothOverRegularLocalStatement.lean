import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧ (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧ Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  first | exact @GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | exact GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | (intros; apply GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular <;> assumption)
