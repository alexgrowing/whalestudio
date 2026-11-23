import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), ‖((deg (A := A) (B := A) f : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  first | (exact @GlobalTheory.AV.AbVar.norm_deg_eq_norm_det) | (exact GlobalTheory.AV.AbVar.norm_deg_eq_norm_det) | (intros; apply GlobalTheory.AV.AbVar.norm_deg_eq_norm_det  <;> assumption)
