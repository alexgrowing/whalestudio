import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_lift_squareZero_thickening : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  first | exact @GlobalTheory.AmpleThickening.relAmple_of_sq_zero | exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero | (intros; apply GlobalTheory.AmpleThickening.relAmple_of_sq_zero <;> assumption)
