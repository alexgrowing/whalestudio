import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull j), (∃ i, σ.f i ≠ 0) → ∃ (c : K) (s : LB.Sec M), c ≠ 0 ∧ (∀ i, (j.app (M.U i)).hom (s.f i) = cst fK (j ⁻¹ᵁ M.U i) c * rs XK (le_pull M j le_rfl) (σ.f (fun _ => i))) ∧ ∃ x ∈ Out.nonzeroLocus s, f x = IsLocalRing.closedPoint O := by
  first | exact @GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | exact GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | (intros; apply GlobalTheory.exists_smul_sec_nonzero_on_special_fibre <;> assumption)
