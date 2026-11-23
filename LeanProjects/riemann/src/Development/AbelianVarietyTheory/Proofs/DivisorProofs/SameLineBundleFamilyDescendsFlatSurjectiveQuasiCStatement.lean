import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiC
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  first | exact @GlobalTheory.DualCon.same_of_fpqc | exact GlobalTheory.DualCon.same_of_fpqc | (intros; apply GlobalTheory.DualCon.same_of_fpqc <;> assumption)
