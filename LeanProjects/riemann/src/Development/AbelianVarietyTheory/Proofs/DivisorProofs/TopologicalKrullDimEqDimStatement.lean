import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_abVar_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  first | exact @GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | exact GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | (intros; apply GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim <;> assumption)
