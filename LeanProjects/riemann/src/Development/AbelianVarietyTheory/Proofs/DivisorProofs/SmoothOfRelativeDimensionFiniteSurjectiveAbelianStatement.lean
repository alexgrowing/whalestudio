import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom := by
  first | exact @GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
