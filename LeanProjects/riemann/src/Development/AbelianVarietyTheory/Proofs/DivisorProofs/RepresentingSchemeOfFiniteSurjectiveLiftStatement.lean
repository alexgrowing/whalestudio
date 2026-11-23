import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representingScheme_of_finite_surjective_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (B S' : Over (Sp R)) (b : B ⟶ S') (P : LB (A ⊗ B).left), IsFinite S'.hom → Surjective S'.hom → Rep A b P → GlobalTheory.DualCon.Good g b.left → (∀ x : B.left, LiftAt A g b P x) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_liftAt | exact GlobalTheory.DualCon.hasRep_of_liftAt | (intros; apply GlobalTheory.DualCon.hasRep_of_liftAt <;> assumption)
