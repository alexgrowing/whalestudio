import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left], IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left) (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB → ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  first | exact @GlobalTheory.Pinch.exists_fam_of_pull | exact GlobalTheory.Pinch.exists_fam_of_pull | (intros; apply GlobalTheory.Pinch.exists_fam_of_pull <;> assumption)
