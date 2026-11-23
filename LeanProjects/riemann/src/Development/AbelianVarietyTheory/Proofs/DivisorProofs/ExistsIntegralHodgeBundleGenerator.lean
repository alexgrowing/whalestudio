import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentificationStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem exists_isFrame_top_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] (F : (Sp R).Modules) {r : ℕ}
    (h : IsVB F r) : ∃ e : Fin r → Γ(F, ⊤), IsFrame e := by
  obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint R)
  have hU : U = ⊤ := by
    refine top_le_iff.1 fun p _ => ?_
    exact (IsLocalRing.specializes_closedPoint p).mem_open U.isOpen hx
  subst hU
  exact ⟨e, he⟩

theorem spMap_jK {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) :
    spMap gam ≫ jK R = jK W ≫ spMap φ := by
  have e : gam.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext hgam
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem relDim {S' : Scheme.{0}} {g : ℕ} {G : Over S'} [GrpObj G] (hGg : SmoothOfRelativeDimension g G.hom)
    {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] (hG₁ : IsSemiAbelian G₁)
    {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left}
    (hα : IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α) : SmoothOfRelativeDimension g G₁.hom := by
  have := hG₁.smooth
  have h₁ : SmoothOfRelativeDimension g ((Over.pullback (jK R)).obj G₁).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hα.1 hGg
  exact GlobalTheory.SmoothRelDim.smoothOfRelativeDimension_of_generic R G₁ (FractionRing R)
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) g h₁

theorem exists_integral_hodgeGen : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  intro S' g G _ _ hG hGg R _ _ _ _ _ G₁ _ _ hG₁ y α hα
  haveI := hG; haveI := hG₁
  haveI : SmoothOfRelativeDimension g G₁.hom := relDim hGg hG₁ hα
  obtain ⟨ε, hε⟩ := exists_isFrame_top_of_isLocalRing R (omega G₁) (isVB_omega G₁ g)
  have p₁ := isGrpPullback_pullback G₁ (jK R)
  have ha : IsFrame fun i => (omegaBase p₁).app ⊤ (pullbackSections (jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (jK R) hε le_top).map_iso _
  refine ⟨gen hα ha, GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hα ha, ?_⟩
  intro W _ _ _ hW φ gam hgam χ' hχ
  haveI : IsDiscreteValuationRing W := hW.1
  obtain ⟨ρ', ψ', hρ', hψ', e₁, e₂⟩ := GlobalTheory.T.traitPullback_semiAbelianModel_identification hG hG₁ hα φ gam hgam χ' hχ
  have pW := isGrpPullback_pullback G₁ (spMap φ)
  have ha' : IsFrame fun i => (omegaBase pW).app ⊤ (pullbackSections (spMap φ) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (spMap φ) hε le_top).map_iso _
  refine ⟨gen hψ' ha', GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hψ' ha', fun z J hJ => ?_⟩
  have q := isGrpPullback_pullback ((Over.pullback (jK R)).obj G₁) (spMap gam)
  have hA := q.comp hα
  have hq₁ := q.comp p₁
  have hb : IsFrame fun i => (omegaBase hq₁).app ⊤ (pullbackSections (spMap gam ≫ jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb _ hε le_top).map_iso _
  refine (GlobalTheory.T.hodge_frame_generator_value_pullback hα ha (spMap gam) q _ _ hA rfl rfl hb (fun i => ?_) z J hJ).trans
    (GlobalTheory.T.hodge_frame_generator_value_pullback hψ' ha' (jK W) hρ' _ _ hA hχ.symm e₁ hb (fun i => ?_) z J hJ).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp p₁ q hq₁ rfl rfl le_top le_top le_top (ε i)).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp pW hρ' hq₁ (spMap_jK φ gam hgam).symm e₂ le_top le_top le_top (ε i)).symm

end GlobalTheory.HodgeFrameGen
