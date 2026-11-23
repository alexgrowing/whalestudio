import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambda
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  first | exact @GlobalTheory.DualCover.exists_cover | exact GlobalTheory.DualCover.exists_cover | (intros; apply GlobalTheory.DualCover.exists_cover <;> assumption)
