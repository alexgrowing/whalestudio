import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

structure BlowupChart {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (s : Fin m) where
  domain : X₁.Opens
  domain_le : domain ≤ π ⁻¹ᵁ U
  chart : EtaleChart (π ≫ p) domain m
  comm : chart.map ≫ coordBlowupSubstMap k m S s = π.resLE U domain domain_le ≫ c.map

private theorem exists_opens_isPullback_of_opens {X₁ M : Scheme.{u}} (V : X₁.Opens)
    (q : V.toScheme ⟶ M) (W : M.Opens) :
    ∃ (dom : X₁.Opens) (_hle : dom ≤ V) (g : dom.toScheme ⟶ W.toScheme)
      (r : dom.toScheme ⟶ V.toScheme),
      IsPullback g r W.ι q ∧ r ≫ V.ι = dom.ι ∧
        ∀ y, q.base y ∈ W → V.ι.base y ∈ dom := by
  classical
  have hdle : Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι) ≤ V := by
    rintro x ⟨y, rfl⟩
    have h1 : V.ι.base ((q ⁻¹ᵁ W).ι.base y) ∈ Set.range V.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).toScheme ≅
      (q ⁻¹ᵁ W).toScheme,
      e.hom ≫ ((q ⁻¹ᵁ W).ι ≫ V.ι) = (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι :=
    ⟨IsOpenImmersion.isoOfRangeEq (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι
        ((q ⁻¹ᵁ W).ι ≫ V.ι) (Scheme.Opens.range_ι _),
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  refine ⟨Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι), hdle, e.hom ≫ (q ∣_ W),
    e.hom ≫ (q ⁻¹ᵁ W).ι, ?_, ?_, ?_⟩
  · have h1 : IsPullback e.hom (e.hom ≫ (q ⁻¹ᵁ W).ι) ((q ⁻¹ᵁ W).ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict q W)
    rwa [Category.id_comp] at h2
  · rw [Category.assoc]
    exact he
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem exists_blowupChart_family_isPullback_covering {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ F : ∀ s : Fin m, s ∈ S → BlowupChart π c S s,
      (∀ (s : Fin m) (hs : s ∈ S),
          IsPullback (F s hs).chart.map
            (π.resLE U (F s hs).domain (F s hs).domain_le)
            (coordBlowupSubstMap k m S s) c.map) ∧
      (∀ x : ↥X₁, x ∈ π ⁻¹ᵁ U → ∃ (s : Fin m) (hs : s ∈ S), x ∈ (F s hs).domain) := by
  classical
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : AlgebraicGeometry.Flat c.map := inferInstance
  have hcomap : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, hZ, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  have hres : Blowup.IsBlowupAlongIdealSheaf (π ∣_ U) ((coordSubspaceIdeal k m S).comap c.map) := by
    have h1 := hπ.restrict U
    rwa [hcomap] at h1
  obtain ⟨q, -, hq⟩ := (isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap k m S).exists_isPullback_of_flat c.map hres
  have key : ∀ (s : Fin m) (hs : s ∈ S), ∃ B : BlowupChart π c S s,
      IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map ∧
        ∀ y, q.base y ∈ Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs) →
          (π ⁻¹ᵁ U).ι.base y ∈ B.domain := by
    intro s hs
    obtain ⟨dom, hle, g, r, hpb, hrι, hmem⟩ :=
      exists_opens_isPullback_of_opens (π ⁻¹ᵁ U) q (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    have hrange : Set.range (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι.base
        = Set.range (affineSpaceCoordBlowupChart k m S s hs).base :=
      Scheme.Opens.range_ι (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    obtain ⟨eW, heW⟩ : ∃ e : (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).toScheme ≅
        affineSpaceFin k m,
        e.hom ≫ coordBlowupSubstMap k m S s =
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫ affineSpaceCoordBlowupMap k m S := by
      refine ⟨IsOpenImmersion.isoOfRangeEq
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
          (affineSpaceCoordBlowupChart k m S s hs) hrange ≪≫ specCoordBlowupChartRingIsoAffineSpace k m S s hs, ?_⟩
      have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
        (affineSpaceCoordBlowupChart k m S s hs) hrange
      rw [Iso.trans_hom, Category.assoc, ← affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap,
        ← Category.assoc, hfac]
    have heW' : eW.inv ≫ (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫
        affineSpaceCoordBlowupMap k m S = coordBlowupSubstMap k m S s := by
      rw [← heW, Iso.inv_hom_id_assoc]
    have hleft : r ≫ (π ∣_ U) = π.resLE U dom hle := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
        ← Category.assoc, hrι]
    have hsq : IsPullback (g ≫ eW.hom) (π.resLE U dom hle) (coordBlowupSubstMap k m S s) c.map := by
      have h1 : IsPullback (g ≫ eW.hom) (𝟙 _) eW.inv g :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      have h2 := h1.paste_vert (hpb.paste_vert hq)
      rwa [Category.id_comp, hleft, heW'] at h2
    have hetale : AlgebraicGeometry.Etale (g ≫ eW.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip c.isEtale
    refine ⟨⟨dom, hle, ⟨g ≫ eW.hom, ?_, hetale⟩, hsq.w⟩, hsq, hmem⟩
    calc (g ≫ eW.hom) ≫ affineSpaceFinToSpec k m
        = (g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m := by
          rw [coordBlowupSubstMap_comp_affineSpaceFinToSpec]
      _ = ((g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m := by
          simp only [Category.assoc]
      _ = (π.resLE U dom hle ≫ c.map) ≫ affineSpaceFinToSpec k m := by rw [hsq.w]
      _ = π.resLE U dom hle ≫ c.map ≫ affineSpaceFinToSpec k m := by simp only [Category.assoc]
      _ = π.resLE U dom hle ≫ U.ι ≫ p := by rw [c.comp_struct]
      _ = (π.resLE U dom hle ≫ U.ι) ≫ p := by simp only [Category.assoc]
      _ = (dom.ι ≫ π) ≫ p := by rw [Scheme.Hom.resLE_comp_ι]
      _ = dom.ι ≫ π ≫ p := by simp only [Category.assoc]
  choose F hF1 hF2 using key
  refine ⟨F, hF1, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have hy : q.base y ∈
      (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2)) := by
    rw [iSup_opensRange_affineSpaceCoordBlowupChart k m S]
    simp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i.1, i.2, hF2 i.1 i.2 y hi⟩

def blowupChartOfIsBlowup {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) : BlowupChart π c S s :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose s hs

theorem isPullback_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) :
    IsPullback (blowupChartOfIsBlowup π c S hπ hZ s hs).chart.map
      (π.resLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le)
      (coordBlowupSubstMap k m S s) c.map :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.1 s hs

theorem exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ (s : Fin m) (hs : s ∈ S), x ∈ (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.2 x hx

end FunctorialResolution.EmbeddedResolution

end
