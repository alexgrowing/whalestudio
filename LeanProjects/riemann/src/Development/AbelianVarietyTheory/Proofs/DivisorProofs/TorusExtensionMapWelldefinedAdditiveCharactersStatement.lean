import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionMap_welldefined_additive_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X), IsMonHom b → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ g : GtPtF D₁ F, ∃! g' : GtPtF D₂ F, Act D₁ D₂ b h g g') ∧ (∀ (g₁ g₂ g₃ : GtPtF D₁ F) (g₁' g₂' g₃' : GtPtF D₂ F), g₁.IsAdd g₂ g₃ → Act D₁ D₂ b h g₁ g₁' → Act D₁ D₂ b h g₂ g₂' → Act D₁ D₂ b h g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ ∀ (t : Multiplicative D₁.X →* Fˣ) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), IsTor t g → Act D₁ D₂ b h g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative h)) g' := by
  first | exact @GlobalTheory.Mum.Two.act_two_hom | exact GlobalTheory.Mum.Two.act_two_hom | (intros; apply GlobalTheory.Mum.Two.act_two_hom <;> assumption)
