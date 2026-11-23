import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens) :
    X.IdealSheafData :=
  (Scheme.Opens.ι W ≫ Z.subschemeι).ker

theorem openSubschemeKer_eq_ker {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens) :
    openSubschemeKer Z W = (Scheme.Opens.ι W ≫ Z.subschemeι).ker := rfl

theorem support_openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)
    (hW : IsClosed (W : Set Z.subscheme)) :
    ((openSubschemeKer Z W).support : Set X) = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  have hcomp : ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base ∘ ⇑(Scheme.Opens.ι W).base := rfl
  have hrange : Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
    rw [hcomp, Set.range_comp, hrangeW]
  rw [openSubschemeKer_eq_ker, Scheme.Hom.support_ker]
  show closure (Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base)
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  rw [hrange]
  exact hclosed.closure_eq

private theorem exists_isIso_openSubschemeKer_subscheme {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) :
    ∃ e : W.toScheme ⟶ (openSubschemeKer Z W).subscheme, IsIso e ∧
      e ≫ (openSubschemeKer Z W).subschemeι = Scheme.Opens.ι W ≫ Z.subschemeι := by
  have : IsClosedImmersion (Scheme.Opens.ι W) := W.isClosedImmersion_ι_of_isClosed hW
  have : IsClosedImmersion (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hker : (Scheme.Opens.ι W ≫ Z.subschemeι).ker = (openSubschemeKer Z W).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι (openSubschemeKer Z W)).symm
  refine ⟨IsClosedImmersion.lift (openSubschemeKer Z W).subschemeι
      (Scheme.Opens.ι W ≫ Z.subschemeι) (le_of_eq hker.symm), ?_,
    IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (Scheme.Opens.ι W ≫ Z.subschemeι)
    (openSubschemeKer Z W).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hker

theorem smooth_subschemeι_openSubschemeKer_comp {X S : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (g : X ⟶ S)
    [Smooth (Z.subschemeι ≫ g)] :
    Smooth ((openSubschemeKer Z W).subschemeι ≫ g) := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_openSubschemeKer_subscheme Z W hW
  have := he
  have hsm : Smooth (Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  have hfac2 : inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g
      = (openSubschemeKer Z W).subschemeι ≫ g := by
    rw [← Category.assoc (Scheme.Opens.ι W) Z.subschemeι g, ← hfac, Category.assoc,
      IsIso.inv_hom_id_assoc]
  have key : Smooth (inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  rwa [hfac2] at key

private theorem comap_eq_ker_fst {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    I.comap f = (Limits.pullback.fst f I.subschemeι).ker := rfl

private theorem comap_opensι_eq_ker_morphismRestrict {T : Scheme.{u}} (K : T.IdealSheafData)
    (V : T.Opens) : K.comap (Scheme.Opens.ι V) = (K.subschemeι ∣_ V).ker := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  rw [comap_eq_ker_fst, ← hfac, Scheme.Hom.ker_comp_of_isIso]

private theorem image_preimage_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Scheme.Opens.ι V ''ᵁ (Scheme.Opens.ι V ⁻¹ᵁ O) = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_eq_right.mpr ?_
  intro x hx
  show x ∈ Set.range ⇑(Scheme.Opens.ι V).base
  rw [Scheme.Opens.range_ι]
  exact h hx

private theorem injective_app_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Function.Injective (CommRingCat.Hom.hom ((Scheme.Opens.ι V).app O)) := by
  have hb := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V) O
    (Scheme.Opens.ι V ⁻¹ᵁ O) le_rfl (image_preimage_opensι_of_le V O h)
  rw [Scheme.Hom.app_eq_appLE]
  exact hb.1

private theorem ker_app_morphismRestrict_eq_map_ker {Y T : Scheme.{u}} (m : Y ⟶ T) (V : T.Opens)
    (P : V.toScheme.affineOpens)
    (e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) :
    RingHom.ker (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
      = Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι V)
            (Scheme.Opens.ι V ''ᵁ P.1) P.1 e))
          (RingHom.ker (CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1)))) := by
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le ..
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_opensι_of_le (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq
    (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1))
    ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
  have hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫
        (m ∣_ V).app P.1
      = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫
        Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m,
      Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1
        ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl,
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1)
        (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) le_rfl hpre2.le]
    exact AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) _ _ _ _
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]

theorem restrictIdeal_openSubschemeKer_of_preimage_le {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : (Z.subschemeι ⁻¹ᵁ U) ≤ W) :
    restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun V _ hVc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hVc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hqc1 : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := inferInstance
  have hqc2 : QuasiCompact (Z.subschemeι ∣_ U) := inferInstance
  rw [restrictIdeal_eq_comap_ι (openSubschemeKer Z W) U, restrictIdeal_eq_comap_ι Z U,
    comap_opensι_eq_ker_morphismRestrict (openSubschemeKer Z W) U,
    comap_opensι_eq_ker_morphismRestrict Z U]
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι U ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι U)
  have hpre : Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι U).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) := hpre.ge
  have hQU : (Scheme.Opens.ι U ''ᵁ P.1) ≤ U := Scheme.Opens.ι_image_le ..
  have hmono : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ (Z.subschemeι ⁻¹ᵁ U) :=
    fun x hx => hQU hx
  have hOW : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ W := le_trans hmono hU
  have hinjW := injective_app_opensι_of_le W (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) hOW
  have hkerA : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    have h1 := AlgebraicGeometry.Scheme.Hom.ker_apply (openSubschemeKer Z W).subschemeι
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    have h2 := AlgebraicGeometry.Scheme.Hom.ker_apply (Scheme.Opens.ι W ≫ Z.subschemeι)
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    rw [Scheme.IdealSheafData.ker_subschemeι] at h1
    rw [← h1, ← h2, openSubschemeKer_eq_ker]
  have hmain : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    rw [hkerA]
    ext x
    have hfac : (CommRingCat.Hom.hom
          ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) x
        = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app
            (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1))))
          ((CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) x) := by
      show (CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1) ≫
        (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)))) x = _
      rw [CommRingCat.hom_comp, RingHom.comp_apply]
    simp only [RingHom.mem_ker, hfac]
    constructor
    · intro hx
      exact hinjW (hx.trans (map_zero _).symm)
    · intro hx
      exact (congrArg _ hx).trans (map_zero _)
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) P,
    AlgebraicGeometry.Scheme.Hom.ker_apply (Z.subschemeι ∣_ U) P,
    ker_app_morphismRestrict_eq_map_ker (openSubschemeKer Z W).subschemeι U P e,
    ker_app_morphismRestrict_eq_map_ker Z.subschemeι U P e, hmain]

private theorem subsingleton_sections_of_eq_bot {Y : Scheme.{u}} (V : Y.Opens)
    (hV : V = ⊥) : Subsingleton ↥(Y.presheaf.obj (Opposite.op V)) := by
  have h : CategoryTheory.Limits.IsTerminal (Y.presheaf.obj (Opposite.op V)) :=
    Y.sheaf.isTerminalOfEqEmpty hV
  exact CommRingCat.subsingleton_of_isTerminal h

theorem restrictIdeal_openSubschemeKer_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U) :
    restrictIdeal (openSubschemeKer Z W) U = ⊤ := by
  have hnot : ∀ y : (openSubschemeKer Z W).subscheme,
      (openSubschemeKer Z W).subschemeι.base y ∉ U := by
    intro y hy
    have hmem : (openSubschemeKer Z W).subschemeι.base y ∈ ((openSubschemeKer Z W).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    rw [support_openSubschemeKer Z W hW] at hmem
    obtain ⟨w, hwW, hw⟩ := hmem
    refine hU w hwW ?_
    rw [hw]
    exact hy
  have hempty : ∀ _y : ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme, False := by
    intro y
    have h1 : (Scheme.Opens.ι ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U)).base y ∈
        ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U : Set (openSubschemeKer Z W).subscheme) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self y
    exact hnot _ h1
  have hObot : ∀ O : (((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme).Opens, O = ⊥ := by
    intro O
    refine le_antisymm ?_ bot_le
    intro y _
    exact (hempty y).elim
  have hqcm : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := by
    refine ⟨fun O _ _ => ?_⟩
    have hE : (⇑((openSubschemeKer Z W).subschemeι ∣_ U).base ⁻¹' O) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro _
      exact hempty y
    rw [hE]
    exact isCompact_empty
  rw [restrictIdeal_eq_comap_ι, comap_opensι_eq_ker_morphismRestrict (openSubschemeKer Z W) U]
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hker : RingHom.ker (CommRingCat.Hom.hom
      (((openSubschemeKer Z W).subschemeι ∣_ U).app V.1)) = ⊤ := by
    have := subsingleton_sections_of_eq_bot
      (((openSubschemeKer Z W).subschemeι ∣_ U) ⁻¹ᵁ V.1) (hObot _)
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) V, hker]
  simp

theorem exists_opens_preimage_subschemeι_le {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (x : X)
    (hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ (Z.subschemeι ⁻¹ᵁ U) ≤ W := by
  have hind : Topology.IsInducing ⇑Z.subschemeι.base :=
    Z.subschemeι.isEmbedding.toIsInducing
  obtain ⟨t, ht, hteq⟩ := hind.isOpen_iff.mp W.isOpen
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · have hwt : w ∈ ⇑Z.subschemeι.base ⁻¹' t := by
      rw [hteq]
      exact hw
    exact hwt
  · intro y hy
    have hy' : y ∈ ⇑Z.subschemeι.base ⁻¹' t := hy
    rw [hteq] at hy'
    exact hy'

theorem exists_opens_notMem_image {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (x : X)
    (hx : x ∉ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U := by
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  refine ⟨⟨(⇑Z.subschemeι.base '' (W : Set Z.subscheme))ᶜ, hclosed.isOpen_compl⟩, hx, ?_⟩
  intro w hw hmem
  exact hmem ⟨w, hw, rfl⟩

private theorem ker_app_opensι_comp_subschemeι_eq_of_preimage_le {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)
    (V : X.Opens) (hVW : (Z.subschemeι ⁻¹ᵁ V) ≤ W) :
    RingHom.ker (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V))
      = RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V)) := by
  have hinjW := injective_app_opensι_of_le W (Z.subschemeι ⁻¹ᵁ V) hVW
  ext a
  have hfac : (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V)) a
      = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V)))
        ((CommRingCat.Hom.hom (Z.subschemeι.app V)) a) := by
    show (CommRingCat.Hom.hom (Z.subschemeι.app V ≫
      (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V))) a = _
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
  simp only [RingHom.mem_ker, hfac]
  constructor
  · intro ha
    exact hinjW (ha.trans (map_zero _).symm)
  · intro ha
    exact (congrArg _ ha).trans (map_zero _)

private theorem exists_ideal_basicOpen_eq_span_singleton_of_eq_span {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (s f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1))
    (hJ : J.ideal U = Ideal.span {f}) :
    ∃ f' : Γ(X, X.basicOpen s), f' ∈ nonZeroDivisors Γ(X, X.basicOpen s) ∧
      J.ideal ⟨X.basicOpen s, U.2.basicOpen s⟩ = Ideal.span {f'} := by
  have hmap := J.map_ideal_basicOpen U s
  rw [hJ, Ideal.map_span, Set.image_singleton] at hmap
  have := U.2.isLocalization_basicOpen s
  refine ⟨_, ?_, hmap.symm⟩
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers s) Γ(X, X.basicOpen s) hf

private theorem one_eq_zero_sections_of_eq_bot {Y : Scheme.{u}} (V : Y.Opens) (hV : V = ⊥) :
    (1 : Γ(Y, V)) = 0 := by
  have := subsingleton_sections_of_eq_bot V hV
  exact Subsingleton.elim _ _

theorem isLocallyGeneratedByNonZeroDivisor_openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme))
    (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor Z) : Blowup.IsLocallyGeneratedByNonZeroDivisor (openSubschemeKer Z W) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hpiece : ∀ V : X.affineOpens, (Z.subschemeι ⁻¹ᵁ V.1) ≤ W →
      (openSubschemeKer Z W).ideal V = Z.ideal V := by
    intro V hVW
    have h2 : RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V.1)) = Z.ideal V := by
      rw [← AlgebraicGeometry.Scheme.Hom.ker_apply Z.subschemeι V,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, ker_app_opensι_comp_subschemeι_eq_of_preimage_le Z W V.1 hVW, h2]
  have hpiecetop : ∀ V : X.affineOpens,
      ((Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ V.1) = ⊥ → (openSubschemeKer Z W).ideal V = ⊤ := by
    intro V hbot
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, Ideal.eq_top_iff_one,
      RingHom.mem_ker, map_one]
    exact one_eq_zero_sections_of_eq_bot _ hbot
  intro x
  by_cases hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  · obtain ⟨N, hxN, hNle⟩ := exists_opens_preimage_subschemeι_le Z W x hx
    obtain ⟨U₁, f₁, hxU₁, hf₁, hZU₁⟩ := hZ x
    have hU₁ : IsAffineOpen U₁.1 := U₁.2
    obtain ⟨s, hsN, hxs⟩ := hU₁.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₁
    obtain ⟨f, hf, hZU⟩ := exists_ideal_basicOpen_eq_span_singleton_of_eq_span Z U₁ s f₁ hf₁ hZU₁
    have hVW : (Z.subschemeι ⁻¹ᵁ (X.basicOpen s)) ≤ W := fun v hv => hNle (hsN hv)
    refine ⟨⟨X.basicOpen s, hU₁.basicOpen s⟩, f, hxs, hf, ?_⟩
    exact (hpiece ⟨X.basicOpen s, hU₁.basicOpen s⟩ hVW).trans hZU
  · obtain ⟨N, hxN, hNno⟩ := exists_opens_notMem_image Z W hW x hx
    obtain ⟨U₀, hxU₀⟩ : ∃ U₀ : X.affineOpens, x ∈ U₀.1 := by
      have hx' : x ∈ (⊤ : X.Opens) := Set.mem_univ x
      rw [← iSup_affineOpens_eq_top X] at hx'
      obtain ⟨U₀, hU₀⟩ := Opens.mem_iSup.mp hx'
      exact ⟨U₀, hU₀⟩
    have hU₀ : IsAffineOpen U₀.1 := U₀.2
    obtain ⟨s, hsN, hxs⟩ := hU₀.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₀
    refine ⟨⟨X.basicOpen s, hU₀.basicOpen s⟩, 1, hxs, one_mem _, ?_⟩
    have hbot : (Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ (X.basicOpen s) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro w hw
      have hw2 : Z.subschemeι.base ((Scheme.Opens.ι W).base w) ∈ X.basicOpen s := hw
      have hmem : (Scheme.Opens.ι W).base w ∈ (W : Set Z.subscheme) := by
        rw [← Scheme.Opens.range_ι W]
        exact ⟨w, rfl⟩
      exact absurd (hsN hw2) (hNno _ hmem)
    rw [Ideal.span_singleton_one]
    exact hpiecetop ⟨X.basicOpen s, hU₀.basicOpen s⟩ hbot

end FunctorialResolution.EmbeddedResolution

end
