import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ), (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 := by
  first | exact @GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | exact GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | (intros; apply GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts <;> assumption)
