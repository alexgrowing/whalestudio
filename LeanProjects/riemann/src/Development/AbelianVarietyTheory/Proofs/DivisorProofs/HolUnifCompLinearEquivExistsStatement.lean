import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holUnif_comp_linearEquiv_exists : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  first | exact @GlobalTheory.KeyFam.holUnif_transport_linearEquiv | exact GlobalTheory.KeyFam.holUnif_transport_linearEquiv | (intros; apply GlobalTheory.KeyFam.holUnif_transport_linearEquiv <;> assumption)
