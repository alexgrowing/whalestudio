import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), (n : K) ≠ 0 → Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  first | exact @GlobalTheory.AV.AbVar.card_torsion_pt | exact GlobalTheory.AV.AbVar.card_torsion_pt | (intros; apply GlobalTheory.AV.AbVar.card_torsion_pt <;> assumption)
