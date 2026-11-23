import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

structure PointedIrreducibleClosed (W : Scheme.{u}) where
  S : Set ↥W
  xi : ↥W
  pt : ↥W
  closedS : IsClosed S
  irredS : IsIrreducible S
  genericXi : IsGenericPoint xi S
  memPt : pt ∈ S

structure SmoothVanishingHypotheses (V : VanishingAssignment.{u}) : Prop where
  orderAt_vanishing_eq_one : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), orderAt (V W T) x = 1
  smooth_opens_ι_comp : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p)
  smooth_vanishing_hypersurface : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
        (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((V W T).subschemeι ≫ p) →
        Smooth ((V H.subscheme S).subschemeι ≫ (H.subschemeι ≫ (U.ι ≫ p)))
  smooth_vanishing_opens : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      Smooth ((V U.toScheme S).subschemeι ≫ (U.ι ≫ p))

def SmoothOrderOneCentersIsolated (V : VanishingAssignment.{u}) {k : Type u} [Field k] [CharZero k]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) : Prop :=
  ∀ C : PointedIrreducibleClosed W, Smooth p → m = 1 →
    Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p) →
    (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S) →
    C.xi ∉ (Z.support : Set ↥W) →
    Disjoint C.S Mem →
    (∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x) →
    C.pt ∈ (Z.support : Set ↥W) → False

theorem subset_support_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N : W.IdealSheafData) (T : Set ↥W) (hT : IsClosed T)
    (hagree : ∀ x ∈ T, AgreeNear N (V W ⟨T, hT⟩) x) :
    T ⊆ (N.support : Set ↥W) := by
  intro x hx
  rw [mem_support_iff_of_agreeNear hV (hagree x hx), hV.support_vanishing W ⟨T, hT⟩]
  exact hx

private theorem irreducibleComponents_opens_not_subset_preimage {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (T : Set ↥W) (hT : IsClosed T)
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T) :
    ∀ E ∈ irreducibleComponents ↥(U.toScheme), ¬ E ⊆ U.ι.base ⁻¹' T := by
  intro E hE hsub
  have hEirr : IsIrreducible E := hE.1
  have hrange := hV.range_ι W U
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hmemU : ∀ y : ↥(U.toScheme), U.ι.base y ∈ (U : Set ↥W) := by
    intro y
    rw [← hrange]
    exact Set.mem_range_self y
  obtain ⟨y0, hy0⟩ := hEirr.nonempty
  have himg : IsIrreducible (U.ι.base '' E) := hEirr.image _ hcont.continuousOn
  obtain ⟨Zc, hZpre, hAZ, hZmax⟩ :=
    exists_preirreducible (closure (U.ι.base '' E)) himg.closure.2
  have hZirr : IsIrreducible Zc := ⟨himg.closure.1.mono hAZ, hZpre⟩
  have hZmem : Zc ∈ irreducibleComponents ↥W :=
    ⟨hZirr, fun u hu hZu => (hZmax u hu.2 hZu).le⟩
  have hEZ : E ⊆ U.ι.base ⁻¹' Zc := by
    intro y hy
    exact hAZ (subset_closure ⟨y, hy, rfl⟩)
  have hZU : (Zc ∩ (U : Set ↥W)).Nonempty := ⟨U.ι.base y0, hEZ hy0, hmemU y0⟩
  have hZUirr : IsIrreducible (Zc ∩ (U : Set ↥W)) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open hZirr (hV.isOpen_opens W U) hZU
  have hsubr : (Zc ∩ (U : Set ↥W)) ⊆ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact Set.inter_subset_right
  have hPirr : IsIrreducible (U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W))) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding (hV.isEmbedding_ι W U) hZUirr hsubr
  have hPeq : U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W)) = U.ι.base ⁻¹' Zc := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, hmemU y⟩
  rw [hPeq] at hPirr
  have hpreimageSub : U.ι.base ⁻¹' Zc ⊆ E := hE.2 hPirr hEZ
  have hZT : Zc ∩ (U : Set ↥W) ⊆ T := by
    rintro x ⟨hxZ, hxU⟩
    rw [← hrange] at hxU
    obtain ⟨y, rfl⟩ := hxU
    exact hsub (hpreimageSub hxZ)
  have hZcl : IsClosed Zc := isClosed_of_mem_irreducibleComponents Zc hZmem
  refine hcomp Zc hZmem ?_
  rw [← FunctorialResolution.EmbeddedResolution.closure_inter_open_eq hZcl hZirr (hV.isOpen_opens W U) hZU]
  exact closure_minimal hZT hT

private theorem orderAt_eq_one_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} (C : PointedIrreducibleClosed W)
    (hp : Smooth p)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    {x : ↥W} (hx : x ∈ C.S) : orderAt I x = 1 := by
  rw [hV.orderAt_congr W I (V W ⟨C.S, C.closedS⟩) x (hagree x hx)]
  exact hG.orderAt_vanishing_eq_one k W p hp ⟨C.S, C.closedS⟩ C.irredS hsm hcomp x hx

theorem false_of_smoothOrderOneCentersIsolated_opens {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (I Z : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (hptU : C.pt ∈ (U : Set ↥W))
    (hIso : SmoothOrderOneCentersIsolated V U.toScheme (U.ι ≫ p) (I.comap U.ι) m
      (U.ι.base ⁻¹' Mem) (Z.comap U.ι))
    (hp : Smooth p) (hm : m = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hrange := hV.range_ι W U
  have hxiU : C.xi ∈ (U : Set ↥W) :=
    (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
  have hxiR : C.xi ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hxiU
  have hptR : C.pt ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hptU
  obtain ⟨y0, hy0⟩ := hxiR
  obtain ⟨y1, hy1⟩ := hptR
  have hS'closed : IsClosed (U.ι.base ⁻¹' C.S) := C.closedS.preimage hcont
  have hgen' : IsGenericPoint y0 (U.ι.base ⁻¹' C.S) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U).toIsInducing
      C.genericXi hy0
  have hirr' : IsIrreducible (U.ι.base ⁻¹' C.S) := by
    rw [← hgen']
    exact isIrreducible_singleton.closure
  have hmemPt : y1 ∈ U.ι.base ⁻¹' C.S := by
    show U.ι.base y1 ∈ C.S
    rw [hy1]
    exact C.memPt
  refine hIso ⟨U.ι.base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
    (hG.smooth_opens_ι_comp k W p U hp) hm
    (hG.smooth_vanishing_opens k W p U ⟨C.S, C.closedS⟩ ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl hsm)
    (irreducibleComponents_opens_not_subset_preimage hV W U C.S C.closedS hcomp) ?_ ?_ ?_ ?_
  · intro hmem
    apply hxi
    have h1 : (1 : ℕ∞) ≤ orderAt (Z.comap U.ι) y0 :=
      (one_le_orderAt_iff_mem_support (Z.comap U.ι) y0).mpr hmem
    rw [hV.orderAt_comap W U Z y0, hy0] at h1
    exact (one_le_orderAt_iff_mem_support Z C.xi).mp h1
  · rw [Set.disjoint_left]
    intro y hy hy2
    exact (Set.disjoint_left.mp hdisj hy) hy2
  · intro y hy
    have h1 := hV.agreeNear_comap W U I (V W ⟨C.S, C.closedS⟩) y (hagree _ hy)
    rw [hV.comap_vanishing W ⟨C.S, C.closedS⟩ U ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl] at h1
    exact h1
  · have h1 : (1 : ℕ∞) ≤ orderAt Z C.pt := (one_le_orderAt_iff_mem_support Z C.pt).mpr hpt
    rw [← hy1, ← hV.orderAt_comap W U Z y1] at h1
    exact (one_le_orderAt_iff_mem_support (Z.comap U.ι) y1).mp h1

private theorem false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (N Z : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W))
    (hH : IsSmoothDivisor (U.ι ≫ p) H)
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (J : Option ((H.subscheme).IdealSheafData))
    (hJnone : J = none →
      IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hJcomp : ∀ Jz, J = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ Jz, J = some Jz → ∀ x : ↥(H.subscheme),
      (H.subschemeι ≫ U.ι).base x ∉ Mem →
      ∃ V' : (H.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.ι = ((N.comap U.ι).comap H.subschemeι).comap V'.ι)
    (ih : ∀ Jz, J = some Jz →
      SmoothOrderOneCentersIsolated V H.subscheme (H.subschemeι ≫ (U.ι ≫ p)) Jz μ
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) ((Z.comap U.ι).comap H.subschemeι))
    (hp : Smooth p) (hm : μ = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hxiS : C.xi ∈ C.S := C.genericXi.mem
  have hordxi : orderAt N C.xi = 1 :=
    orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagree hxiS
  have hxiN : C.xi ∈ (N.support : Set ↥W) :=
    (one_le_orderAt_iff_mem_support N C.xi).mp (le_of_eq hordxi.symm)
  cases hJ : J with
  | none =>
    exact false_of_isOpen_preimage_support hV W N Z
      ⟨C.S, C.S, C.xi, C.xi, C.pt, C.closedS, C.closedS, C.irredS, C.irredS, C.genericXi,
        C.genericXi, C.memPt, C.memPt⟩ U H hptU hpt hZH hNsubH (hJnone hJ) hxi hxiN
  | some Jz =>
    have hIH := ih Jz hJ
    have hxiU : C.xi ∈ (U : Set ↥W) :=
      (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
    have hCsubN : C.S ⊆ (N.support : Set ↥W) :=
      subset_support_of_agreeNear hV W N C.S C.closedS hagree
    have hsubH : (U.ι.base ⁻¹' C.S) ⊆ (H.support : Set ↥(U.toScheme)) := by
      intro y hy
      apply hNsubH
      rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
      exact hCsubN hy
    obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.xi hxiU hxiS
    obtain ⟨y1, hy1⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.pt hptU C.memPt
    have hS'closed : IsClosed ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isClosed_preimage_subschemeι_comp_ι hV W U H C.S C.closedS
    have hgen' : IsGenericPoint y0 ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isGenericPoint_preimage_subschemeι_comp_ι hV W U H C.S C.xi C.genericXi y0 hy0
    have hirr' : IsIrreducible ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) := by
      rw [← hgen']
      exact isIrreducible_singleton.closure
    have hmemPt : y1 ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      show (H.subschemeι ≫ U.ι).base y1 ∈ C.S
      rw [hy1]
      exact C.memPt
    have hagree' : ∀ x ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S,
        AgreeNear Jz (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x := by
      intro x hx
      have h1 : AgreeNear ((N.comap U.ι).comap H.subschemeι)
          (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x :=
        hV.agreeNear_vanishing_restrict W N U H ⟨C.S, C.closedS⟩
          ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ x rfl hsubH (hagree _ hx)
      have h2 : AgreeNear Jz ((N.comap U.ι).comap H.subschemeι) x :=
        hJloc Jz hJ x (Set.disjoint_left.mp hdisj hx)
      exact hV.agreeNear_trans H.subscheme Jz ((N.comap U.ι).comap H.subschemeι)
        (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x h2 h1
    have hS'J : ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) ⊆ (Jz.support : Set ↥(H.subscheme)) :=
      subset_support_of_agreeNear hV H.subscheme Jz ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        hS'closed hagree'
    have hcomp' : ∀ E ∈ irreducibleComponents ↥(H.subscheme),
        ¬ E ⊆ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      intro E hE hEsub
      exact hV.not_subset_support_of_nonzeroOnComponents H.subscheme Jz (hJcomp Jz hJ) E hE
        (hEsub.trans hS'J)
    have hsupp : ∀ x : ↥(H.subscheme),
        x ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) ↔
          (H.subschemeι ≫ U.ι).base x ∈ (Z.support : Set ↥W) := by
      intro x
      constructor
      · intro hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at hx
          exact hx
        have h2 : (U.ι.base (H.subschemeι.base x)) ∈ (Z.support : Set ↥W) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at h1
          exact h1
        rw [hV.base_comp]
        exact h2
      · intro hx
        rw [hV.base_comp] at hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
          exact hx
        rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
        exact h1
    have hxi' : y0 ∉ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      intro hmem
      apply hxi
      have h1 := (hsupp y0).mp hmem
      rw [hy0] at h1
      exact h1
    have hpt' : y1 ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      refine (hsupp y1).mpr ?_
      rw [hy1]
      exact hpt
    have hdisj' : Disjoint ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact (Set.disjoint_left.mp hdisj hx) hx2
    have hsmooth : Smooth (H.subschemeι ≫ (U.ι ≫ p)) :=
      ((isSmoothDivisor_iff (U.ι ≫ p) H).mp hH).2
    have hsmV : Smooth ((V H.subscheme
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩).subschemeι ≫
        (H.subschemeι ≫ (U.ι ≫ p))) :=
      hG.smooth_vanishing_hypersurface k W p U H hH ⟨C.S, C.closedS⟩
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ rfl hsubH hsm
    exact hIH ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
      hsmooth hm hsmV hcomp' hxi' hdisj' hagree' hpt'

theorem smoothOrderOneCentersIsolated_of_principalizationCertificate {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ => SmoothOrderOneCentersIsolated V W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => SmoothOrderOneCentersIsolated V W p N μ Mem Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p I m Mem Z hm2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p I m Mem Z M N μ hI hM hmu hZc hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hIN : ∀ x ∈ C.S, AgreeNear I N x := by
      intro x hx
      have hxM : x ∉ (M.support : Set ↥W) := fun hmm =>
        (Set.disjoint_left.mp hdisj hx) (hM hmm)
      obtain ⟨Uc, hUcx, hUcdisj⟩ :
          ∃ Uc : W.Opens, x ∈ Uc ∧ Disjoint ((Uc : Set ↥W)) (M.support : Set ↥W) :=
        ⟨⟨(M.support : Set ↥W)ᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hxM,
          disjoint_compl_left⟩
      refine ⟨Uc, hUcx, ?_⟩
      have hMtop : M.comap Uc.ι = ⊤ := FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint M Uc hUcdisj
      rw [hI, hV.comap_mul W Uc.toScheme Uc.ι M N, hMtop, hV.top_mul]
    have hagreeN : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x := fun x hx =>
      hV.agreeNear_trans W N I (V W ⟨C.S, C.closedS⟩) x (agreeNear_symm (hIN x hx)) (hagree x hx)
    rcases Nat.lt_or_ge μ 2 with h2 | h2
    · have hmu1 : μ = 1 := by omega
      exact ih C hp hmu1 hsm hcomp hxi hdisj hagreeN hpt
    · have hord : orderAt N C.pt = 1 :=
        orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagreeN C.memPt
      have hmem : C.pt ∈ orderAtLeastLocus N μ := hZc hpt
      rw [FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff, hord] at hmem
      have hle : μ ≤ 1 := by exact_mod_cast hmem
      omega
  · intro W p I m Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p I Z m Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p N μ Mem Z hmu2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p N μ Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p N Z μ Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih C hp hm hsm hcomp hxi
      hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated hV hG p N Z μ Mem C (U C.pt hz) (H C.pt hz) (hU C.pt hz) (hH C.pt hz)
      (hNsubH C.pt hz) (hZH C.pt hz) (J C.pt hz) (hJnone C.pt hz) (hJcomp C.pt hz)
      (hJloc C.pt hz) (fun Jz hJ => ih C.pt hz Jz hJ) hp hm hsm hcomp hxi hdisj hagree hpt

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
