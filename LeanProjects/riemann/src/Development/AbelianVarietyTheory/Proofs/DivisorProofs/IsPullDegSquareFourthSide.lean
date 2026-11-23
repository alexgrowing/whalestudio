import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
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

noncomputable section

namespace GlobalTheory.PullSquare

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_of_eq {θ θ' : R →+* R'} (e : θ = θ') {D : DegPre R} {D' : DegPre R'} (r : IsPullDeg θ D D') :
    ∃ r' : IsPullDeg θ' D D', (∀ x, r'.xe x = r.xe x) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g : GtPtF D F)
        (g' : GtPtF D' F), IsPullGtF θ r F g g' → IsPullGtF θ' r' F g g' := by
  subst e
  exact ⟨r, fun _ => rfl, fun _ _ _ _ _ _ h => h⟩

end GlobalTheory.PullSquare

theorem GlobalTheory.Mum.isPullDeg_square : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  intro R R₁ W W₁ _ _ _ _ _ _ _ _ I I₁ J J₁ _ _ _ _ ρ φ iw φ₁ hsq hφ₁ hρi hφi hiw D D₁ D' D'₁ hρ hD hX
  obtain ⟨r, Tr⟩ := GlobalTheory.LabTrans.exists_comp hφi hiw hD hX
  obtain ⟨r', hx', hg'⟩ := GlobalTheory.PullSquare.exists_of_eq hsq.symm r
  obtain ⟨h, Th⟩ := GlobalTheory.LabTrans.exists_cancel hρi hφ₁ hρ r'
  refine ⟨h, fun x => ?_, ?_⟩
  · rw [Th.xe_eq, hx', ← Tr.xe_eq]
  · intro F _ _ _ _ _ cρ cφ ci c₁ g g₁ g' g'₁ Hρ HD HX
    have cθ : GlobalTheory.ArcPull.Compat (iw.comp φ) F := fun a => (cφ a).trans (ci (φ a))
    have cθ' : GlobalTheory.ArcPull.Compat (φ₁.comp ρ) F := fun a => (cρ a).trans (c₁ (ρ a))
    have H : IsPullGtF (φ₁.comp ρ) r' F g g'₁ := hg' F g g'₁ (Tr.isPullGtF cθ HD HX)
    obtain ⟨g'', H''⟩ := GlobalTheory.ArcPull.exists_pullGt h GlobalTheory.ExpansionTotal.globalFns c₁ g₁
    have H2 := Th.isPullGtF cθ' Hρ H''
    rwa [GlobalTheory.ArcPull.pullGt_unique r' cθ' H2 H] at H''
