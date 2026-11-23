import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) → IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 → ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  first | exact @GlobalTheory.LBLift.exists_pic_of_strict_lift | exact GlobalTheory.LBLift.exists_pic_of_strict_lift | (intros; apply GlobalTheory.LBLift.exists_pic_of_strict_lift <;> assumption)
