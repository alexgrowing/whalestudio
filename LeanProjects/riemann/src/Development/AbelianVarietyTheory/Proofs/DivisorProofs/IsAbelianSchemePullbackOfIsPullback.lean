import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_pullback_of_isPullback : ∀ (S T S' : Scheme.{0}) (G : Over S) [GrpObj G] (t : T ⟶ S) (A : Over S') [GrpObj A] (a : pullback G.hom t ⟶ A.left) (g : T ⟶ S'), IsSemiAbelian G → IsAbelianScheme A → IsPullback a (pullback.snd G.hom t) A.hom g → IsAbelianScheme ((Over.pullback t).obj G) := by
  intro S T S' G _ t A _ a g hG hA sq
  exact
  { comm := by have := hG.comm; infer_instance
    smooth := by have := hG.smooth; change Smooth (pullback.snd G.hom t); infer_instance
    proper := by
      have := hA.proper; change IsProper (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    geomConnected := by
      have := hA.geomConnected; change GeometricallyConnected (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq inferInstance }

theorem ampleDiv_closure_on_chart : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ D : CartierDiv A.left, AmpleDiv D → LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (ρ : R₀ →+* R), ρ.Flat → ρ f ≠ 0 → ∀ (G : Over (Sp R)) [GrpObj G] [IsIntegral G.left], IsSemiAbelian G → ∀ (V : G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* G.left.functionField) (D₁ : CartierDiv G.left), (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) → IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ awayMap f) (spMap ρ) → ∀ (y : Sp (FractionRing R) ⟶ Sp (Localization.Away f)) (α : pullback G.hom (jK R) ⟶ A.left), IsGrpPullback ((Over.pullback (jK R)).obj G) A y α → (∀ (T : Scheme.{0}) (t : T ⟶ pullback G.hom (jK R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ α = t' ≫ φ) → PFF V.ι φ θ → PPull V.ι φ θ D D₁ → AmpleDiv D₁ := by
  intro R₀ _ _ f A _ _ hA D hD hsym R _ _ _ _ hR ρ hflat hρf G _ _ hG V φ θ D₁ hV hsq y α hα hcomp hff hpp
  obtain ⟨g, l, hl, sq⟩ := GlobalTheory.GenericFibreChart.exists_isPullback_generic R₀ f A R ρ hρf G V φ hV hsq
  have hGK : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    isAbelianScheme_pullback_of_isPullback _ _ _ G (jK R) A (l ≫ φ) g hG hA sq
  haveI : IsProper ((Over.pullback (jK R)).obj G).hom := hGK.proper
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hAD : IsAmpleLB (toLB D) := (ampleDiv_iff_isAmpleLB A.left D).1 hD
  have h1 : IsAmpleLB ((toLB D).pull (l ≫ φ)) := hAD.pull_of_isPullback sq
  have h3 : LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := GlobalTheory.Desc.PullOpen.lbIso_pull _ _ V φ θ D D₁ hff hpp
  have hL₁ := isLB_toLB D₁
  have h4 : LBIso ((toLB D₁).pull (pullback.fst G.hom (jK R))) ((toLB D).pull (l ≫ φ)) := by
    rw [← hl]
    exact LBIso.trans (LB.isLB_pull hL₁ _) (LB.isLB_pull (LB.isLB_pull hL₁ _) _)
      (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL₁ V.ι l).symm
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull hL₁ _) _) (LB.isLB_pull (LB.isLB_pull (isLB_toLB D) _) _)
        (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.Mum.UExt.lbIso_pull h3 l)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (isLB_toLB D) φ l))
  have h5 : IsAmpleLB ((toLB D₁).pull (pullback.fst G.hom (jK R))) := h1.of_lbIso (LB.isLB_pull hL₁ _) h4
  have h6 := (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_pull hL₁ _)).2 h5
  have hlα : α = l ≫ φ := by
    have := hcomp _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rwa [Category.id_comp] at this
  have hs1 := GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback _ _ A ((Over.pullback (jK R)).obj G) y α hα (toLB D) (isLB_toLB D) hsym
  rw [hlα] at hs1
  have hK₁ := LB.isLB_pull hL₁ (pullback.fst G.hom (jK R))
  have hK := LB.isLB_pull (isLB_toLB D) (l ≫ φ)
  have hs2 : LBIso (((toLB D₁).pull (pullback.fst G.hom (jK R))).pull
      (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left)
      ((toLB D₁).pull (pullback.fst G.hom (jK R))) :=
    LBIso.trans (LB.isLB_pull hK₁ _) (LB.isLB_pull hK _) hK₁ (GlobalTheory.Mum.UExt.lbIso_pull h4 _)
      (LBIso.trans (LB.isLB_pull hK _) hK hK₁ hs1 h4.symm)
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hs3 := GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre R G hG (toLB D₁) hL₁ hs2
  have h7 := GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian R hR G hG hGK (toLB D₁) hL₁ h6 hs3
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact (ampleDiv_iff_isAmpleLB G.left D₁).2 h7

end GlobalTheory.Desc
