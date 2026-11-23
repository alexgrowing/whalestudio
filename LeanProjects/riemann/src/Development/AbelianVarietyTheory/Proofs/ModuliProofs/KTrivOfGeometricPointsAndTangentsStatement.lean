import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_geometric_points_and_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  first | exact @GlobalTheory.KCriterion.kTriv_of_points_of_tangents | exact GlobalTheory.KCriterion.kTriv_of_points_of_tangents | (intros; apply GlobalTheory.KCriterion.kTriv_of_points_of_tangents <;> assumption)
