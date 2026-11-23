import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'), (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧ (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  first | exact @GlobalTheory.DualCon.hasRep_baseChange_iff | exact GlobalTheory.DualCon.hasRep_baseChange_iff | (intros; apply GlobalTheory.DualCon.hasRep_baseChange_iff <;> assumption)
