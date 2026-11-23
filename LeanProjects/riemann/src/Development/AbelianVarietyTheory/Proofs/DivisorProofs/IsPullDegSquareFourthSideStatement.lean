import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSide
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullDeg_square_fourth_side : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  first | exact @GlobalTheory.Mum.isPullDeg_square | exact GlobalTheory.Mum.isPullDeg_square | (intros; apply GlobalTheory.Mum.isPullDeg_square <;> assumption)
