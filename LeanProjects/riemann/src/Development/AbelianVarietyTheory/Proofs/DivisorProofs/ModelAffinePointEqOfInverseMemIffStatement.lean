import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  first | exact @GlobalTheory.Points.point_eq_of_inv_mem_iff | exact GlobalTheory.Points.point_eq_of_inv_mem_iff | (intros; apply GlobalTheory.Points.point_eq_of_inv_mem_iff <;> assumption)
