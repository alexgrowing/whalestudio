import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim : ∀ (K : Type) [Field K] (A B : AbVar K), Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧ Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  first | (exact @GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (exact GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (intros; apply GlobalTheory.AV.AbVar.hom_finite_free_rank_le  <;> assumption)
