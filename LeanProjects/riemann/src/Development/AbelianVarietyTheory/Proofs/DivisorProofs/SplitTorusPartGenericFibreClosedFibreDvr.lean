import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingClosedAllFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

theorem pullTorus_left_comp_iso (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ h.1.isoPullback.hom = (bcIso f X).hom.left ≫ ((Over.pullback f).map i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullTorus_left, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.fst G.hom f = pullback.fst (splitTorus S X).hom f ≫ i.left := by
      simp; exact pullback.lift_fst _ _ _
    rw [this, ← Category.assoc, GlobalTheory.SplitTorus.bcIso_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.snd G.hom f = pullback.snd (splitTorus S X).hom f := by
      simp; exact pullback.lift_snd _ _ _
    rw [this, Over.w (pullTorus h i)]
    exact (Over.w (bcIso f X).hom).symm

theorem mono_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion ((Over.pullback f).map i).left) : Mono (pullTorus h i) := by
  have k := pullTorus_left_comp_iso h i
  have : Mono ((bcIso f X).hom.left ≫ ((Over.pullback f).map i).left) := inferInstance
  rw [← k] at this
  have : Mono (pullTorus h i).left := mono_of_mono _ h.1.isoPullback.hom
  exact (Over.forget _).mono_of_mono_map this

theorem closedImm_of_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion (pullTorus h i).left) : IsClosedImmersion ((Over.pullback f).map i).left := by
  have k := pullTorus_left_comp_iso h i
  have e : ((Over.pullback f).map i).left = (bcIso f X).inv.left ≫ (pullTorus h i).left ≫ h.1.isoPullback.hom := by
    rw [k, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  haveI : IsIso (bcIso f X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (bcIso f X).inv))
  rw [e]
  infer_instance

theorem isClosedImmersion_of_isTorPart {tι : splitTorus S X ⟶ G} (h : IsTorPart tι) : IsClosedImmersion tι.left := by
  obtain ⟨-, B, _, q, hB, -, hk⟩ := h
  have h₁ : IsClosedImmersion (η[B].left ≫ B.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[B].left := IsClosedImmersion.of_comp _ B.hom
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂

theorem isIso_torusMap (T : Scheme.{0}) {Y : Type} [AddCommGroup Y] (e : X ≃+ Y) :
    IsIso (torusMap T e.toAddMonoidHom) :=
  ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩

end General

theorem spMap_fractionRing_closedPoint (V : Type) [CommRing V] [IsDomain V] :
    (spMap (algebraMap V (FractionRing V))) (closedPoint (FractionRing V)) = genericPoint (Sp V) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V (FractionRing V)) (maximalIdeal (FractionRing V)) = ⊥
  rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V _)

theorem bijective_of_mono_torusMap {κ : Type} [Field κ] {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁]
    [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [Module.Free ℤ X₁] [Module.Finite ℤ X₁]
    (hr : Module.finrank ℤ X₀ = Module.finrank ℤ X₁) (ρ : X₀ →+ X₁) [Mono (torusMap (Sp κ) ρ)] :
    Function.Bijective ρ := by
  have hs : Function.Surjective ρ := by
    let l : X₁ →+ X₁ ⧸ ρ.range := QuotientAddGroup.mk' ρ.range
    have e : torusMap (Sp κ) l ≫ torusMap (Sp κ) ρ =
        torusMap (Sp κ) (0 : X₁ →+ X₁ ⧸ ρ.range) ≫ torusMap (Sp κ) ρ := by
      rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
      congr 1
      ext x
      simp [l]
    have e2 := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
    intro y
    have hy : QuotientAddGroup.mk' ρ.range y = 0 := DFunLike.congr_fun e2 y
    obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨x, hx⟩
  let e₀ : X₁ ≃ₗ[ℤ] X₀ := LinearEquiv.ofFinrankEq X₁ X₀ hr.symm
  have hinj := OrzechProperty.injective_of_surjective_endomorphism (e₀.toLinearMap ∘ₗ ρ.toIntLinearMap)
    (e₀.surjective.comp hs)
  exact ⟨fun a b hab => hinj (by simp [hab]), hs⟩

end GlobalTheory.Poinc.FibClosed

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

theorem isTorPart_pullTorus_closed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  intro V _ _ _ G₁ _ _ hG X₁ _ _ _ j hj GK _ ψ hψ hgen κ _ b hb G₀ _ ψ₀ hψ₀ X₀ _ _ _ t₀ ht₀ hr
  haveI := hj
  let e : X₁ ≃+ (Fin (Module.finrank ℤ X₁) → ℤ) := (Module.finBasis ℤ X₁).equivFun.toAddEquiv
  let u : splitTorus (Sp V) (Fin (Module.finrank ℤ X₁) → ℤ) ⟶ G₁ := torusMap (Sp V) e.toAddMonoidHom ≫ j
  have hu : IsMonHom u := inferInstance
  have hgenU : ∀ (k : Type) [Field k] (g : Sp k ⟶ Sp V), g (closedPoint k) = genericPoint (Sp V) →
      IsClosedImmersion ((Over.pullback g).map u).left := by
    intro k _ g hg
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue u k g, hg, ← spMap_fractionRing_closedPoint V,
      ← GlobalTheory.TorusFibreImm.closedImm_iff_residue u (FractionRing V) _]
    refine closedImm_of_pullTorus hψ u ?_
    rw [pullTorus_torusMap_comp, Over.comp_left]
    haveI := isClosedImmersion_of_isTorPart hgen
    haveI := isIso_torusMap (Sp (FractionRing V)) e
    haveI : IsIso (torusMap (Sp (FractionRing V)) e.toAddMonoidHom).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (torusMap (Sp (FractionRing V)) e.toAddMonoidHom)))
    infer_instance
  have hsp := GlobalTheory.TorusFibre.isClosedImmersion_special_of_local V (FractionRing V) G₁ hG _ u hu
    (by
      haveI := hgenU (FractionRing V) _ (spMap_fractionRing_closedPoint V)
      exact (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono ((Over.pullback (spMap (algebraMap V (FractionRing V)))).map u).left)))
  have hfib : IsClosedImmersion ((Over.pullback (spMap b)).map u).left := by
    have h2 := (GlobalTheory.TorusFibreImm.closedImm_iff_residue u (ResidueField V) _).1 hsp
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V)))) (closedPoint (ResidueField V)) =
        (spMap b) (closedPoint κ) :=
      (IsLocalRing.comap_closedPoint (residue V)).trans (IsLocalRing.comap_closedPoint b).symm
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue, ← h3]
    exact h2
  have hmono : Mono (pullTorus hψ₀ u) := mono_pullTorus hψ₀ u hfib
  have hmono' : Mono (pullTorus hψ₀ j) := by
    have k : pullTorus hψ₀ j = torusMap _ e.symm.toAddMonoidHom ≫ pullTorus hψ₀ u := by
      rw [pullTorus_torusMap_comp, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X₁ from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
    haveI := isIso_torusMap (Sp κ) e.symm
    rw [k]
    infer_instance
  obtain ⟨ρ, hρ⟩ := ht₀.factor (pullTorus hψ₀ j) inferInstance
  haveI : Mono (torusMap (Sp κ) ρ) := by
    rw [hρ] at hmono'
    exact mono_of_mono _ t₀
  have hbij := bijective_of_mono_torusMap (κ := κ) hr ρ
  have h := ht₀.equiv (AddEquiv.ofBijective ρ hbij)
  rw [hρ]
  exact h

end GlobalTheory.Poinc.FibClosed
