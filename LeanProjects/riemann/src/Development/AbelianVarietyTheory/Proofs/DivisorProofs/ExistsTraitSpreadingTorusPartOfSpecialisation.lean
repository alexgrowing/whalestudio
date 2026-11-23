import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.NonlocalTrait in

theorem exists_trait_torusPart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  intro Y _ _ G _ _ hG w w' hsp hne
  let s' : Sp (Y.presheaf.stalk w') ⟶ Y := Y.fromSpecStalk w'
  let g : Y.presheaf.stalk w' →+* Y.presheaf.stalk w := (Y.presheaf.stalkSpecializes hsp).hom
  have hgs : spMap g ≫ s' = Y.fromSpecStalk w := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hg : ¬ IsLocalHom g := by
    intro hl
    apply hne
    have h1 : (spMap g) (closedPoint (Y.presheaf.stalk w)) = closedPoint (Y.presheaf.stalk w') :=
      Spec_closedPoint
    calc w = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := Scheme.fromSpecStalk_closedPoint.symm
      _ = (spMap g ≫ s') (closedPoint (Y.presheaf.stalk w)) := by rw [hgs]
      _ = s' ((spMap g) (closedPoint (Y.presheaf.stalk w))) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  let GR := (Over.pullback s').obj G
  have hGR : IsSemiAbelian GR := IsSemiAbelian.pullback _ G hG
  obtain ⟨V, _, _, hV, ψ, Ω, _, α, β, hψ, hβ, e, ⟨E⟩⟩ :=
    GlobalTheory.exists_trait_nonlocal_torusExtension (Y.presheaf.stalk w') GR hGR (Y.presheaf.stalk w) g hg
  let alg := algebraMap V (FractionRing V)
  let ξ : Sp V ⟶ Y := spMap ψ ≫ s'
  let G₁ := (Over.pullback ξ).obj G
  have h₁ : IsGrpPullback G₁ G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback _ G hG
  let GK := (Over.pullback (spMap (alg.comp ψ))).obj GR
  have hK : IsGrpPullback GK G (spMap alg ≫ ξ) _ :=
    ((isGrpPullback_pullback GR (spMap (alg.comp ψ))).comp (isGrpPullback_pullback G s')).congr
      (by rw [spMap_comp', Category.assoc]) rfl
  let ψ' : GK.left ⟶ G₁.left := h₁.1.lift _ (GK.hom ≫ spMap alg) (by rw [hK.1.w, Category.assoc])
  have hψ' : IsGrpPullback GK G₁ (spMap alg) ψ' :=
    h₁.cancel (hK.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _)
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  obtain ⟨j, hj, ej⟩ := GlobalTheory.TorusPart.extend_torus_hom_dvr V G₁ hG₁ GK ψ' hψ' ⟨E⟩ (FractionRing V) (RingHom.id _) GK ψ'
    hψ' E.X E.i E.i_hom
  haveI : IsLocalHom ψ := hψ
  have hαl : IsLocalHom α := ⟨fun x hx => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx⟩
  have hβl : IsLocalHom β := ⟨fun x hx => by
    by_contra hn
    rw [hβ x ((mem_maximalIdeal x).2 hn)] at hx
    exact not_isUnit_zero hx⟩
  have key : spMap α ≫ spMap alg ≫ ξ = spMap β ≫ Y.fromSpecStalk w := by
    calc spMap α ≫ spMap alg ≫ ξ = spMap ((α.comp alg).comp ψ) ≫ s' := by
          simp only [ξ, spMap_comp', Category.assoc]
      _ = spMap (β.comp g) ≫ s' := by rw [e]
      _ = spMap β ≫ Y.fromSpecStalk w := by rw [spMap_comp', Category.assoc, hgs]
  refine ⟨V, inferInstance, inferInstance, hV, ξ, G₁, inferInstance, inferInstance, pullback.fst G.hom ξ, E.X,
    inferInstance, inferInstance, inferInstance, j, GK, inferInstance, ψ', hψ', ?_, ?_, h₁, hj, ?_⟩
  · have h1 : (spMap ψ) (closedPoint V) = closedPoint (Y.presheaf.stalk w') := Spec_closedPoint
    calc ξ (closedPoint V) = s' ((spMap ψ) (closedPoint V)) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  · have h1 : (spMap α) (closedPoint Ω) = closedPoint (FractionRing V) := Spec_closedPoint
    have h2 : (spMap β) (closedPoint Ω) = closedPoint (Y.presheaf.stalk w) := Spec_closedPoint
    calc (spMap alg ≫ ξ) (closedPoint (FractionRing V)) = (spMap alg ≫ ξ) ((spMap α) (closedPoint Ω)) := by rw [h1]
      _ = (spMap α ≫ spMap alg ≫ ξ) (closedPoint Ω) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap β ≫ Y.fromSpecStalk w) (closedPoint Ω) := by rw [key]
      _ = Y.fromSpecStalk w ((spMap β) (closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
      _ = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := by rw [h2]
      _ = w := Scheme.fromSpecStalk_closedPoint
  · have : GlobalTheory.TorusPart.pullTorus hψ' j = E.i := ej
    rw [this]
    exact isTorPart_torusExtension E

end GlobalTheory.Poinc.FibLat
