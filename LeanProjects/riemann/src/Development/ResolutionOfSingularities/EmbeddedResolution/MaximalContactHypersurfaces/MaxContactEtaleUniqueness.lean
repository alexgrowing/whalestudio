import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFiberProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCommonCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.EtaleMaxContactComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactChartUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.StalkIdealSpreadOut
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_comp_eq_of_comap_comap_eq {A B C : Scheme.{u}} (ι : A ⟶ B) (F G : B ⟶ C)
    (I J : C.IdealSheafData) (h : (I.comap F).comap ι = (J.comap G).comap ι) :
    I.comap (ι ≫ F) = J.comap (ι ≫ G) := by
  have hF : I.comap (ι ≫ F) = (I.comap F).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  have hG : J.comap (ι ≫ G) = (J.comap G).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [hF, hG]
  exact h

private theorem comap_comp_ι_eq_comap_restrictIdeal {Y Z : Scheme.{u}} (J : Y.IdealSheafData)
    (U : Y.Opens) (g : Z ⟶ U.toScheme) : J.comap (g ≫ U.ι) = (restrictIdeal J U).comap g := by
  show J.comap (g ≫ U.ι) = (J.comap U.ι).comap g
  simp [Scheme.IdealSheafData.comap_comp]

private theorem exists_subscheme_comap_lift {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    ∃ θ : (I.comap f).subscheme ⟶ I.subscheme,
      θ ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  have h2 : Scheme.Hom.ker I.subschemeι ≤
      Scheme.Hom.ker ((I.comap f).subschemeι ≫ f) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.IdealSheafData.le_map_comap I f
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι _ h2,
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι _ h2⟩

private theorem range_base_subset_range_preimage_ι {T W Z S : Scheme.{u}} (tι : T ⟶ W) (ιZ : W ⟶ Z)
    (θ : T ⟶ S) (σ : S ⟶ Z) (hθ : θ ≫ σ = tι ≫ ιZ) (Wop : Z.Opens)
    (hsub : Set.range ⇑ιZ.base ⊆ (Wop : Set ↥Z)) :
    Set.range ⇑θ.base ⊆ Set.range ⇑((σ ⁻¹ᵁ Wop).ι).base := by
  rw [Scheme.Opens.range_ι]
  rintro z ⟨y, rfl⟩
  show σ.base (θ.base y) ∈ Wop
  have hb : (θ ≫ σ).base y = (tι ≫ ιZ).base y := by rw [hθ]
  have hb2 : σ.base (θ.base y) = ιZ.base (tι.base y) := hb
  rw [hb2]
  exact hsub ⟨tι.base y, rfl⟩

private theorem comp_eq_of_lift_comp_eq {T W Z S S' Q : Scheme.{u}}
    (tι : T ⟶ W) (ιZ : W ⟶ Z) (σ : S ⟶ Z) (j : S' ⟶ S) (θ : T ⟶ S) (δ : T ⟶ S')
    (F G : Z ⟶ Q) (hθ : θ ≫ σ = tι ≫ ιZ) (hδ : δ ≫ j = θ)
    (heq : j ≫ σ ≫ F = j ≫ σ ≫ G) :
    tι ≫ ιZ ≫ F = tι ≫ ιZ ≫ G := by
  have h1 : tι ≫ ιZ ≫ F = δ ≫ j ≫ σ ≫ F := by
    rw [← Category.assoc tι ιZ F, ← hθ, ← hδ]
    simp only [Category.assoc]
  have h2 : tι ≫ ιZ ≫ G = δ ≫ j ≫ σ ≫ G := by
    rw [← Category.assoc tι ιZ G, ← hθ, ← hδ]
    simp only [Category.assoc]
  rw [h1, h2, heq]

theorem nonempty_etaleMaxContactComparison (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂)
    (pt : P) (hpt : pt ∈ orderAtLeastLocus A μ) :
    Nonempty (EtaleMaxContactComparison k p A μ N H₁ H₂ pt) := by
  obtain ⟨V, hVaff, hptV, n, c₁, c₂, γ, j₀, hH₁, hH₂, hmc₁, hmc₂, hgm₁, hgm₂, hco, hNγ,
      _, hγne⟩ :=
    exists_common_charts_of_isMaxContactHypersurface A hμ N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt
  have hlftF : LocallyOfFiniteType (chartPullbackFst c₁ c₂ ≫ p) := inferInstance
  have hln1 : IsLocallyNoetherian (chartPullback c₁ c₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (f := chartPullbackFst c₁ c₂ ≫ p)
  have hln2 : IsLocallyNoetherian
      ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subscheme := by
    have : LocallyOfFiniteType
        (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          (chartPullbackFst c₁ c₂ ≫ p)) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian
      (f := ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
        (chartPullbackFst c₁ c₂ ≫ p))
  obtain ⟨hagree, Wop, hptW, hstalk, _, heqmor, hHcomap, hcoordS⟩ :=
    exists_opens_chartPullback_eq_of_mem_maxContactIdeal k p A hμ hinv hVaff c₁ c₂ j₀
      (fun i hi => (hco i hi).symm) pt hptV
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₁ j₀).mp hmc₁)
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₂ j₀).mp hmc₂)
      hgm₁ hgm₂ (mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hμ hpt)
  obtain ⟨U0, hU0⟩ : ∃ U0 : (chartPullback c₁ c₂).affineOpens,
      chartPullbackPoint c₁ c₂ pt hptV hagree ∈ U0.1 := by
    have hx : chartPullbackPoint c₁ c₂ pt hptV hagree ∈
        (⨆ U : (chartPullback c₁ c₂).affineOpens, (U : (chartPullback c₁ c₂).Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top (chartPullback c₁ c₂)]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, hU⟩
  obtain ⟨g, hgle, hw0W'⟩ :=
    U0.2.exists_basicOpen_le (⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hptW⟩ : Wop) hU0
  have hW'aff : IsAffineOpen ((chartPullback c₁ c₂).basicOpen g) :=
    ((chartPullback c₁ c₂).affineBasicOpen g).2
  have hetale1 : AlgebraicGeometry.Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hetale2 : AlgebraicGeometry.Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂) := inferInstance
  have hsmooth1 : AlgebraicGeometry.Smooth
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hlft1 : LocallyOfFiniteType
      ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p) := inferInstance
  have e1 : H₁.comap (chartPullbackFst c₁ c₂)
      = (c₁.coordIdeal {j₀}).comap (Limits.pullback.fst c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal H₁ V (Limits.pullback.fst c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.fst c₁.map c₂.map)) hH₁)
  have e2 : H₂.comap (chartPullbackSnd c₁ c₂)
      = (c₂.coordIdeal {j₀}).comap (Limits.pullback.snd c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal H₂ V (Limits.pullback.snd c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.snd c₁.map c₂.map)) hH₂)
  have e3 : H₁.comap (chartPullbackFst c₁ c₂) = H₂.comap (chartPullbackSnd c₁ c₂) :=
    e1.trans (hHcomap.trans e2.symm)
  refine ⟨{ W := ((chartPullback c₁ c₂).basicOpen g).toScheme
          , f₁ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂
          , f₂ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂
          , w := ⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hw0W'⟩
          , isAffine := hW'aff
          , etale_f₁ := hetale1
          , etale_f₂ := hetale2
          , lft_f₁ := hlft1
          , base_f₁ := ?_
          , base_f₂ := ?_
          , comap_A := ?_
          , comap_H := ?_
          , comap_N := ?_
          , comp_p := ?_
          , maxContact_comp := ?_ }⟩
  · exact chartPullbackFst_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · exact chartPullbackSnd_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) A A ?_
    exact restrictIdeal_eq_of_stalkIdeal_eq _ _ ((chartPullback c₁ c₂).basicOpen g)
      (fun y hy => hstalk y (hgle hy))
  · refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) H₁ H₂ ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) e3
  · intro J hJ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hJ
    have key : (N[i]'hi).comap (chartPullbackFst c₁ c₂) = (N[i]'hi).comap (chartPullbackSnd c₁ c₂) := by
      obtain ⟨hnone, hsome⟩ := hNγ i hi
      have h0F : (N[i]'hi).comap (chartPullbackFst c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.fst c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal _ V _
      have h0G : (N[i]'hi).comap (chartPullbackSnd c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.snd c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal _ V _
      rw [h0F, h0G]
      cases hγ : γ i with
      | none =>
        rw [hnone hγ, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.comap_top]
      | some jj =>
        have hjj : jj ≠ j₀ := by
          intro h
          exact hγne i (by rw [hγ, h])
        have hnotmem : j₀ ∉ ({jj} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          exact fun h => hjj h.symm
        rw [hsome jj hγ, chartPullback_comap_coordIdeal_eq c₁ c₂ {jj}, hcoordS {jj} hnotmem]
    refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) (N[i]'hi) (N[i]'hi) ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) key
  · have hcs := chartPullbackFst_comp_eq_chartPullbackSnd_comp c₁ c₂
    simp only [Category.assoc] at hcs ⊢
    rw [hcs]
  · have hNeq : maxContactIdeal k
          ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p)
          (A.comap (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂)) μ
        = ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
            ((chartPullback c₁ c₂).basicOpen g).ι := by
      simp only [maxContactIdeal_eq_derivIdealSheafIterate]
      rw [derivIdealSheafIterate_comap k p
        (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) (μ - 1) A]
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hNeq]
    obtain ⟨θ, hθ⟩ :=
      exists_subscheme_comap_lift ((chartPullback c₁ c₂).basicOpen g).ι
        ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂))
    have hsub : Set.range ⇑(((chartPullback c₁ c₂).basicOpen g).ι).base ⊆
        (Wop : Set ↥(chartPullback c₁ c₂)) := by
      rw [Scheme.Opens.range_ι]
      intro z hz
      exact hgle hz
    have hrange := range_base_subset_range_preimage_ι
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
        ((chartPullback c₁ c₂).basicOpen g).ι).subschemeι)
      ((chartPullback c₁ c₂).basicOpen g).ι θ
      (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι) hθ Wop hsub
    exact comp_eq_of_lift_comp_eq _ _ _
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ Wop).ι)
      θ (IsOpenImmersion.lift _ θ hrange) (chartPullbackFst c₁ c₂) (chartPullbackSnd c₁ c₂)
      hθ (IsOpenImmersion.lift_fac _ θ hrange) heqmor

theorem exists_etale_equalizing_isMaxContactHypersurface (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (_horder : ∀ x : P, orderAt A x ≤ (μ : ℕ∞))
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ :=
  exists_etale_maxContactIdeal_comparison k p A μ N H₁ H₂
    (fun pt hpt =>
      nonempty_etaleMaxContactComparison k p A hμ hinv N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt)

end FunctorialResolution.EmbeddedResolution
