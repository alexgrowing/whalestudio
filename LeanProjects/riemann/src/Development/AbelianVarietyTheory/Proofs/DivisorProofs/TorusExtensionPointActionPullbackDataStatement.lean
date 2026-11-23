import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPointAction_pullback_data : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  first | exact @GlobalTheory.Mum.Two.ActPull.main | exact GlobalTheory.Mum.Two.ActPull.main | (intros; apply GlobalTheory.Mum.Two.ActPull.main <;> assumption)
