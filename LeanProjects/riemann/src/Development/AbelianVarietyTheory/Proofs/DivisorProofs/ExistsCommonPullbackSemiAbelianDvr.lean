import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem exists_common_pullback_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  intro Y G _ hG V _ _ Gu _ hGu V' _ _ _ fV ξ AK _ α Ψ hα hΨ
  let j : Sp (FractionRing V') ⟶ Sp V' := spMap (algebraMap V' (FractionRing V'))
  have hα' : IsGrpPullback AK Gu (j ≫ spMap fV) α := by
    have := hα; rwa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at this
  have hG'p := isGrpPullback_pullback Gu (spMap fV)
  have hG''p := isGrpPullback_pullback G ξ
  let ω : AK.left ⟶ ((Over.pullback (spMap fV)).obj Gu).left :=
    pullback.lift α (AK.hom ≫ j) (by rw [hα'.1.w, Category.assoc])
  have hωf : ω ≫ pullback.fst Gu.hom (spMap fV) = α := pullback.lift_fst _ _ _
  have hωs : ω ≫ ((Over.pullback (spMap fV)).obj Gu).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω : IsGrpPullback AK ((Over.pullback (spMap fV)).obj Gu) j ω :=
    IsGrpPullback.cancel hG'p (IsGrpPullback.congr hα' rfl hωf.symm) hωs
  let ω'' : AK.left ⟶ ((Over.pullback ξ).obj G).left :=
    pullback.lift Ψ (AK.hom ≫ j) (by rw [hΨ.1.w, Category.assoc])
  have hω''f : ω'' ≫ pullback.fst G.hom ξ = Ψ := pullback.lift_fst _ _ _
  have hω''s : ω'' ≫ ((Over.pullback ξ).obj G).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω'' : IsGrpPullback AK ((Over.pullback ξ).obj G) j ω'' :=
    IsGrpPullback.cancel hG''p (IsGrpPullback.congr hΨ rfl hω''f.symm) hω''s
  have hG' : IsSemiAbelian ((Over.pullback (spMap fV)).obj Gu) := IsSemiAbelian.pullback _ _ hGu
  have hG'' : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback _ _ hG
  obtain ⟨E, ⟨hE, hEω⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec V')
    (GlobalTheory.IsGenericPointHom.fractionField V' (FractionRing V')) hG' hG'' hω hω''
  haveI := hE
  let β' := E.hom.left ≫ pullback.fst G.hom ξ
  have hβ' : IsGrpPullback ((Over.pullback (spMap fV)).obj Gu) G ξ β' :=
    IsGrpPullback.congr ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp hG''p) (Category.id_comp _) rfl
  have hωβ' : ω ≫ β' = Ψ := by
    show ω ≫ E.hom.left ≫ pullback.fst G.hom ξ = Ψ
    rw [← Category.assoc, hEω, hω''f]
  refine ⟨(Over.pullback (spMap fV)).obj Gu, inferInstance, pullback.fst _ _, β', ω, hG'p, hβ', hωs, hωf, hωβ', ?_⟩
  intro F f eK hF hf
  let F' := (Over.pullback (spMap fV)).map F
  have hF'f : F'.left ≫ pullback.fst Gu.hom (spMap fV) = pullback.fst Gu.hom (spMap fV) ≫ F.left :=
    pullback.lift_fst _ _ _
  refine ⟨F', hF'f, ?_⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG'
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V' (FractionRing V')
  haveI : IsSchemeTheoreticallyDominant ω := .of_isPullback hω.1.flip
  have key : ω ≫ F'.left = eK.left ≫ ω := by
    apply pullback.hom_ext
    · rw [Category.assoc, hF'f, ← Category.assoc, hωf, Category.assoc, hωf, hF]
    · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
      have e2 : eK.left ≫ AK.hom = AK.hom := Over.w eK
      show (ω ≫ F'.left) ≫ ((Over.pullback (spMap fV)).obj Gu).hom = (eK.left ≫ ω) ≫ ((Over.pullback (spMap fV)).obj Gu).hom
      rw [Category.assoc, e1, hωs, Category.assoc, hωs, ← Category.assoc, e2]
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ ω ?_
  · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
    have e2 : f.left ≫ G.hom = G.hom := Over.w f
    rw [Category.assoc, hβ'.1.w, ← Category.assoc, e1, Category.assoc, e2, hβ'.1.w]
  · rw [← Category.assoc, key, Category.assoc, hωβ', ← Category.assoc, hωβ', hf]

end GlobalTheory.Poinc.FibLat
