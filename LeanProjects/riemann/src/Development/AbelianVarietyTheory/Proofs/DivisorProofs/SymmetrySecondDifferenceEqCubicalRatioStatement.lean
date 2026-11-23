import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatio
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ = val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  first | exact @GlobalTheory.PolDeg.SymCube.sym_cube | exact GlobalTheory.PolDeg.SymCube.sym_cube | (intros; apply GlobalTheory.PolDeg.SymCube.sym_cube <;> assumption)
