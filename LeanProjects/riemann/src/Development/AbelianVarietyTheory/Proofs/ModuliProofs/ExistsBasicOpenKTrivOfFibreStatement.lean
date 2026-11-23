import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_kTriv_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K) (A₀ : Over (Sp K)) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsGrpPullback A₀ A (spMap x) φ₀ → Out.KTriv A₀ (L.pull φ₀) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (A' : Over (Sp R')) [GrpObj A'] (π : A'.left ⟶ A.left), IsUnit (φ f) → IsGrpPullback A' A (spMap φ) π → Out.KTriv A' (L.pull π) := by
  first | exact @GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit | exact GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit | (intros; apply GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit <;> assumption)
