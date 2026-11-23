import Development.EtaleCohomology.EtaleSheaves.ChartGeoGlue

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartGeoPf

theorem chartStdGeo_pf : ChartStdGeo := by
  intro X S p n _ x W hxW
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) x
  obtain ⟨g, hgW, hxg⟩ := hV.exists_basicOpen_le ⟨x, hxW⟩ hxV
  refine ⟨U, hU, X.basicOpen g, hV.basicOpen g, (X.basicOpen_le g).trans e, hxg, hgW, ?_⟩
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h3 := h1.comp hf
  rw [zero_add] at h3
  convert h3 using 1
  rw [← Scheme.Hom.appLE_map p e (homOfLE (X.basicOpen_le g)).op]
  rfl

theorem rangeKer_pf : RangeKer := by
  intro X Z ι _ V hV y
  have hy : hV.fromSpec y ∈ V := by
    have h := hV.range_fromSpec
    exact (show hV.fromSpec y ∈ (V : Set X) from h ▸ Set.mem_range_self y)
  have hcl : closure (Set.range ι) = Set.range ι := ι.isClosedEmbedding.isClosed_range.closure_eq
  have key : ∀ f : Γ(X, V), hV.fromSpec y ∈ X.basicOpen f ↔ f ∉ (show PrimeSpectrum Γ(X, V) from y).asIdeal := by
    intro f
    show y ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
    rw [hV.fromSpec_preimage_basicOpen]
    rfl
  rw [← hcl, ← Scheme.Hom.support_ker, SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hy,
    Scheme.Hom.ker_apply, Scheme.mem_zeroLocus_iff]
  simp only [key, not_not]
  rfl

theorem quotLoc_pf : QuotLoc := by
  intro n A B T _ _ _ _ π hπ hloc P hP hI
  obtain ⟨s, hs, H⟩ := hloc
  have hPb : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ (by simpa using hI)
  obtain ⟨t, hts, htP⟩ : ∃ t ∈ s, t ∉ P.map π := by
    by_contra! hc
    exact hPb.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  obtain ⟨g, rfl⟩ := hπ t
  have hg : g ∉ P := fun h => htP (Ideal.mem_map_of_mem π h)
  refine ⟨g, hg, ?_⟩
  set φ : Localization.Away g →+* Localization.Away (π g) := Localization.awayMap π g with hφ
  have hsurj : Function.Surjective φ := by
    rw [hφ, Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    exact ⟨b, 0, by simp⟩
  have hker : RingHom.ker φ = (RingHom.ker π).map (algebraMap B (Localization.Away g)) :=
    IsLocalization.ker_map _ π (Submonoid.map_powers π g)
  let e : (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g))) ≃+*
      Localization.Away (π g) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : (e.symm : Localization.Away (π g) →+* _).comp
      ((algebraMap T (Localization.Away (π g))).comp (π.comp (algebraMap A B))) =
      algebraMap A (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g))) := by
    ext a
    apply e.injective
    simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply, RingEquiv.apply_symm_apply]
    rw [IsScalarTower.algebraMap_apply A B]
    show _ = e (Ideal.Quotient.mk _ (algebraMap B (Localization.Away g) (algebraMap A B a)))
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp [φ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap, ← he]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).1 _ e.symm (H _ hts)

theorem ChartGeo_of_parts (h1 : ChartStdGeo) (h2 : RangeKer) (h3 : QuotLoc) : LateralTheory.E.LeafChartAffPf.ChartGeo := by
  intro X Z S p ι _ d e _ _ x hx W hxW
  obtain ⟨U, hU, V, hV, hUV, hxV, hVW, hstd⟩ := h1 p (e + d) x W hxW
  letI : Algebra Γ(S, U) Γ(X, V) := (p.appLE U V hUV).hom.toAlgebra
  have h0 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension e) (ι ≫ p) inferInstance ⟨U, hU⟩
    ⟨ι ⁻¹ᵁ V, hV.preimage ι⟩ ((le_refl (ι ⁻¹ᵁ V)).trans ((TopologicalSpace.Opens.map ι.base).map (homOfLE hUV)).le)
  rw [← Scheme.Hom.appLE_comp_appLE ι p U V (ι ⁻¹ᵁ V) hUV le_rfl, ← Scheme.Hom.app_eq_appLE,
    CommRingCat.hom_comp] at h0
  refine ⟨Γ(S, U), Γ(X, V), inferInstance, inferInstance, inferInstance, RingHom.ker (ι.app V).hom, hstd,
    fun P hP hI => h3 e _ _ _ (ι.app V).hom (ι.app_surjective V hV) h0 P hP hI,
    hV.fromSpec, inferInstance, ?_, ?_, fun y => h2 ι V hV y⟩
  · rw [hV.range_fromSpec]; exact hxV
  · rw [hV.range_fromSpec]; exact hVW

end LateralTheory.E.ChartGeoPf
