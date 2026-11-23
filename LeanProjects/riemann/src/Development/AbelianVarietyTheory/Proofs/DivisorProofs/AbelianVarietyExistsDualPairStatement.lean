import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_exists_dual_pair : ∀ (K : Type) [Field K] (A : AbVar K), ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  first | exact @GlobalTheory.AV.exists_dualPair | exact GlobalTheory.AV.exists_dualPair | (intros; apply GlobalTheory.AV.exists_dualPair <;> assumption)
