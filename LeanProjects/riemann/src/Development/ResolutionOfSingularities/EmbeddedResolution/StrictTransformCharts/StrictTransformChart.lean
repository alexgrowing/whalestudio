import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def complEmbPreimage (m : ℕ) (S : Finset (Fin m)) (a : Fin m) :
    Finset (Fin (m - ({a} : Finset (Fin m)).card)) :=
  Finset.filter (fun i => complOrderEmb m {a} i ∈ S) Finset.univ

theorem mem_complEmbPreimage (m : ℕ) (S : Finset (Fin m)) (a : Fin m)
    (i : Fin (m - ({a} : Finset (Fin m)).card)) :
    i ∈ complEmbPreimage m S a ↔ complOrderEmb m {a} i ∈ S := by
  simp [complEmbPreimage]

theorem mem_complEmbPreimage_of_complOrderEmb_eq (m : ℕ) (S : Finset (Fin m)) (a : Fin m)
    {s : Fin m} (hs : s ∈ S) {i : Fin (m - ({a} : Finset (Fin m)).card)}
    (hi : complOrderEmb m {a} i = s) : i ∈ complEmbPreimage m S a := by
  rw [mem_complEmbPreimage, hi]
  exact hs

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

private theorem blowupChart_restrict_map_comp_coordBlowupSubstMap (B : BlowupChart π c S s) (V : X₁.Opens)
    (hV : V ≤ B.domain) :
    (B.chart.restrict hV).map ≫ coordBlowupSubstMap k m S s =
      π.resLE U V (hV.trans B.domain_le) ≫ c.map := by
  have key : X₁.homOfLE hV ≫ π.resLE U B.domain B.domain_le
      = π.resLE U V (hV.trans B.domain_le) := by
    apply (cancel_mono (Scheme.Opens.ι U)).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.resLE_comp_ι]
  rw [EtaleChart.restrict_map, Category.assoc, B.comm, ← Category.assoc, key]

def BlowupChart.restrict (B : BlowupChart π c S s) (V : X₁.Opens) (hV : V ≤ B.domain) :
    BlowupChart π c S s where
  domain := V
  domain_le := hV.trans B.domain_le
  chart := B.chart.restrict hV
  comm := blowupChart_restrict_map_comp_coordBlowupSubstMap B V hV

@[simp] theorem BlowupChart.restrict_domain (B : BlowupChart π c S s) (V : X₁.Opens)
    (hV : V ≤ B.domain) : (B.restrict V hV).domain = V := rfl

theorem BlowupChart.restrict_chart (B : BlowupChart π c S s) (V : X₁.Opens)
    (hV : V ≤ B.domain) : (B.restrict V hV).chart = B.chart.restrict hV := rfl

theorem BlowupChart.exists_isAffineOpen_mem_le_domain (B : BlowupChart π c S s) (x : X₁)
    (hx : x ∈ B.domain) :
    ∃ V : X₁.Opens, V ≤ B.domain ∧ IsAffineOpen V ∧ x ∈ V := by
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens hx
  exact ⟨V, hVU, hV, hxV⟩

private theorem opensι_appLE_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appLE V ⊤ (Scheme.Opens.ι_preimage_self V).ge = V.topIso.inv := by
  simp
  rfl

private theorem coordIdeal_ideal_top_eq_map {Y : Scheme.{u}} {K : Type u} [Field K]
    {p' : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} [IsAffine V.toScheme]
    (d : EtaleChart p' V n) (T : Finset (Fin n)) :
    (d.coordIdeal T).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ =
      Ideal.map V.topIso.inv.hom (Ideal.span (d.coord '' (T : Set (Fin n)))) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
    coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.ofIdealTop_ideal_top, Ideal.map_span,
    Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
  exact (CommRingCat.inv_hom_apply V.topIso _).symm

private theorem comap_opensι_ideal_top_eq_map {Y : Scheme.{u}} (J : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) [IsAffine V.toScheme] :
    (J.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
      = Ideal.map V.topIso.inv.hom (J.ideal ⟨V, hV⟩) := by
  rw [← opensι_appLE_top_eq_topIso_inv V]
  exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (Scheme.Opens.ι_preimage_self V).ge

private theorem etaleChart_map_appTop_coord {Y : Scheme.{u}} {K : Type u} [Field K]
    {p' : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (d : EtaleChart p' V n)
    (j : Fin n) :
    (Scheme.Hom.appTop d.map).hom (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j))
      = V.topIso.inv.hom (d.coord j) := by
  rw [EtaleChart.coord_def]
  exact (CommRingCat.inv_hom_apply V.topIso _).symm

private theorem appLE_top_top_eq_appTop {A B : Scheme.{u}} (f : A ⟶ B)
    (e : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : B.Opens)) :
    f.appLE (⊤ : B.Opens) (⊤ : A.Opens) e = Scheme.Hom.appTop f := by
  have h1 : A.presheaf.map (homOfLE e).op = 𝟙 Γ(A, ⊤) := A.presheaf.map_id (op (⊤ : A.Opens))
  calc f.appLE (⊤ : B.Opens) (⊤ : A.Opens) e
      = f.app (⊤ : B.Opens) ≫ A.presheaf.map (homOfLE e).op := rfl
    _ = f.app (⊤ : B.Opens) ≫ 𝟙 Γ(A, ⊤) := by rw [h1]
    _ = Scheme.Hom.appTop f := Category.comp_id _

theorem restrictIdeal_comap_subschemeι_eq_coordIdeal (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z H : X.IdealSheafData) (S : Finset (Fin m)) (a : Fin m)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {a}) :
    restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a) := by
  classical
  have hW : IsAffineOpen (H.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι H hU
  have : IsAffine (H.subschemeι ⁻¹ᵁ U).toScheme := hW
  have hmem : c.coord a ∈ H.ideal ⟨U, hU⟩ := by
    rw [c.ideal_eq_span_coord hU H {a} hH]
    exact Ideal.subset_span ⟨a, by simp, rfl⟩
  have hφa : (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord a) = 0 := by
    have happ := Scheme.IdealSheafData.subschemeι_app H ⟨U, hU⟩
    have hval := congrArg (fun f => (CommRingCat.Hom.hom f) (c.coord a)) happ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hval
    rw [Scheme.Hom.appLE_eq_app, hval,
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hspan : Ideal.span
        ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin m))))
      = Ideal.span ((c.restrictToSubscheme hU H {a} hH).coord ''
          ((complEmbPreimage m S a : Finset (Fin (m - ({a} : Finset (Fin m)).card))) :
            Set (Fin (m - ({a} : Finset (Fin m)).card)))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      by_cases hja : j = a
      · subst hja
        rw [hφa]
        exact Ideal.zero_mem _
      · have hjnot : j ∉ ({a} : Finset (Fin m)) := by simpa using hja
        obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hjnot
        have hiT : i ∈ complEmbPreimage m S a :=
          mem_complEmbPreimage_of_complOrderEmb_eq m S a (Finset.mem_coe.mp hj) hi
        refine Ideal.subset_span ⟨i, Finset.mem_coe.mpr hiT, ?_⟩
        rw [c.restrictToSubscheme_coord hU H {a} hH i, hi]
    · rw [Ideal.span_le]
      rintro x ⟨i, hi, rfl⟩
      rw [c.restrictToSubscheme_coord hU H {a} hH i]
      exact Ideal.subset_span ⟨c.coord (complOrderEmb m {a} i),
        ⟨complOrderEmb m {a} i, Finset.mem_coe.mpr ((mem_complEmbPreimage m S a i).mp
          (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩
  have hideal : (restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)).ideal
        ⟨⊤, isAffineOpen_top (H.subschemeι ⁻¹ᵁ U).toScheme⟩
      = ((c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a)).ideal
        ⟨⊤, isAffineOpen_top (H.subschemeι ⁻¹ᵁ U).toScheme⟩ := by
    rw [restrictIdeal_eq_comap_ι, comap_opensι_ideal_top_eq_map (Z.comap H.subschemeι) hW,
      coordIdeal_ideal_top_eq_map,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE Z H.subschemeι ⟨U, hU⟩
        ⟨H.subschemeι ⁻¹ᵁ U, hW⟩ le_rfl,
      c.ideal_eq_span_coord hU Z S hZ, Ideal.map_span, hspan]
  exact (Scheme.IdealSheafData.equivOfIsAffine
    (X := (H.subschemeι ⁻¹ᵁ U).toScheme)).injective hideal

private theorem strictTransform_preimage_domain_le_preimage (B : BlowupChart π c S s)
    (Z H : X.IdealSheafData)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain ≤ q ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U) := by
  intro y hy
  have h2 : ((Blowup.strictTransform π Z H).subschemeι ≫ π).base y ∈ U := B.domain_le hy
  rw [← hq] at h2
  exact h2

private theorem restrictToSubscheme_map_comp_affineSpaceFinToSpec (B : BlowupChart π c S s)
    (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map ≫
          affineSpaceFinToSpec k (m - ({a} : Finset (Fin m)).card) =
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι ≫ (q ≫ (H.subschemeι ≫ p)) := by
  have h := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
    (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).comp_struct
  rw [h, ← Category.assoc (Blowup.strictTransform π Z H).subschemeι π p, ← hq, Category.assoc]

private theorem restrictToSubscheme_map_comp_coordBlowupSubstMap (B : BlowupChart π c S s)
    (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map ≫
          coordBlowupSubstMap k (m - ({a} : Finset (Fin m)).card) (complEmbPreimage m S a) s' =
      q.resLE (H.subschemeι ⁻¹ᵁ U) ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          (strictTransform_preimage_domain_le_preimage B Z H q hq) ≫
        (c.restrictToSubscheme hU H {a} hH).map := by
  classical
  have hle := strictTransform_preimage_domain_le_preimage B Z H q hq
  have hr : q.resLE (H.subschemeι ⁻¹ᵁ U)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle ≫ (H.subschemeι ⁻¹ᵁ U).ι
      = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι ≫ q := by
    rw [Scheme.Hom.resLE_comp_ι]
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec,
      restrictToSubscheme_map_comp_affineSpaceFinToSpec B hB Z H hs hZ a ha has hH q hq,
      (c.restrictToSubscheme hU H {a} hH).comp_struct]
    simp only [← Category.assoc]
    rw [hr]
  · rintro ⟨i₀⟩
    have hL : ∀ j : Fin (m - ({a} : Finset (Fin m)).card),
        (Scheme.Hom.appTop (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
            (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map).hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j))
          = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv.hom
              (((Blowup.strictTransform π Z H).subschemeι.appLE B.domain
                ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl).hom
                (B.chart.coord (complOrderEmb m {a} j))) := by
      intro j
      rw [etaleChart_map_appTop_coord, EtaleChart.restrictToSubscheme_coord]
    have hM : ∀ j : Fin (m - ({a} : Finset (Fin m)).card),
        (Scheme.Hom.appTop (c.restrictToSubscheme hU H {a} hH).map).hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j))
          = (H.subschemeι ⁻¹ᵁ U).topIso.inv.hom
              ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
                (c.coord (complOrderEmb m {a} j))) := by
      intro j
      rw [etaleChart_map_appTop_coord, EtaleChart.restrictToSubscheme_coord]
    have hkey : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl
          ≫ q.appLE (H.subschemeι ⁻¹ᵁ U)
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle
        = π.appLE U B.domain B.domain_le
          ≫ (Blowup.strictTransform π Z H).subschemeι.appLE B.domain
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl := by
      rw [Scheme.Hom.appLE_comp_appLE q H.subschemeι U (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl hle,
        Scheme.Hom.appLE_comp_appLE (Blowup.strictTransform π Z H).subschemeι π U B.domain
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) B.domain_le le_rfl]
      exact Scheme.Hom.appLE_congr_hom hq _ _ _ _
    have hkeyfun : ∀ x : Γ(X, U),
        (q.appLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle).hom
          ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom x)
        = ((Blowup.strictTransform π Z H).subschemeι.appLE B.domain
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl).hom
          ((π.appLE U B.domain B.domain_le).hom x) := by
      intro x
      have h := congrArg (fun f => (CommRingCat.Hom.hom f) x) hkey
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
      exact h
    have e2 : (⊤ : ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).toScheme.Opens)
        ≤ (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
            ⁻¹ᵁ (⊤ : (H.subschemeι ⁻¹ᵁ U).toScheme.Opens) := by simp
    have hres : (H.subschemeι ⁻¹ᵁ U).topIso.inv ≫
          Scheme.Hom.appTop (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
        = q.appLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle
          ≫ ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv := by
      rw [← opensι_appLE_top_eq_topIso_inv (H.subschemeι ⁻¹ᵁ U),
        ← appLE_top_top_eq_appTop (q.resLE (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle) e2,
        Scheme.Hom.appLE_comp_appLE (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
          (H.subschemeι ⁻¹ᵁ U).ι (H.subschemeι ⁻¹ᵁ U) ⊤ ⊤ (Scheme.Opens.ι_preimage_self _).ge e2,
        ← opensι_appLE_top_eq_topIso_inv
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain),
        Scheme.Hom.appLE_comp_appLE
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι q (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) ⊤ hle
          (Scheme.Opens.ι_preimage_self _).ge]
      exact Scheme.Hom.appLE_congr_hom hr _ _ _ _
    have hstar : ∀ y : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U),
        (Scheme.Hom.appTop (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)).hom
          ((H.subschemeι ⁻¹ᵁ U).topIso.inv.hom y)
        = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv.hom
            ((q.appLE (H.subschemeι ⁻¹ᵁ U)
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle).hom y) := by
      intro y
      have h := congrArg (fun f => (CommRingCat.Hom.hom f) y) hres
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
      exact h
    have hcond : (complOrderEmb m {a} i₀ ∈ S ∧ complOrderEmb m {a} i₀ ≠ s)
        ↔ (i₀ ∈ complEmbPreimage m S a ∧ i₀ ≠ s') := by
      rw [mem_complEmbPreimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hh => h2 (by rw [hh, hs'])⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hh => h2 ((complOrderEmb m {a}).injective (by rw [hh, hs']))⟩
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [coordBlowupSubstMap_appTop_coord, hM i₀, hstar, hkeyfun,
      BlowupChart.appLE_coord B (complOrderEmb m {a} i₀)]
    by_cases hP : complOrderEmb m {a} i₀ ∈ S ∧ complOrderEmb m {a} i₀ ≠ s
    · rw [if_pos hP, if_pos (hcond.mp hP)]
      simp only [map_mul]
      rw [hL i₀, hL s', hs']
    · rw [if_neg hP, if_neg (fun hh => hP (hcond.mpr hh))]
      exact hL i₀

def BlowupChart.restrictToStrictTransform (B : BlowupChart π c S s)
    (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    BlowupChart q (c.restrictToSubscheme hU H {a} hH) (complEmbPreimage m S a) s' where
  domain := (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain
  domain_le := strictTransform_preimage_domain_le_preimage B Z H q hq
  chart :=
    { map := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map
      comp_struct :=
        restrictToSubscheme_map_comp_affineSpaceFinToSpec B hB Z H hs hZ a ha has hH q hq
      isEtale := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).isEtale }
  comm :=
    restrictToSubscheme_map_comp_coordBlowupSubstMap B hU hB Z H hs hZ a ha has hH s' hs' q hq

@[simp] theorem BlowupChart.restrictToStrictTransform_domain (B : BlowupChart π c S s)
    (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).domain =
      (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain := rfl

theorem BlowupChart.restrictToStrictTransform_chart_map (B : BlowupChart π c S s)
    (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart.map =
      (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map := rfl

theorem BlowupChart.strictTransform_subschemeι_preimage_domain_eq_bot (B : BlowupChart π c S s)
    (Z H : X.IdealSheafData) [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {s}) :
    (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain = ⊥ := by
  have htop : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ :=
    B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZ hH
  rw [eq_bot_iff]
  intro y hy
  have hxB : (Blowup.strictTransform π Z H).subschemeι.base y ∈ B.domain := hy
  have hxsupp : (Blowup.strictTransform π Z H).subschemeι.base y ∈ (Blowup.strictTransform π Z H).support := by
    have hr : (Blowup.strictTransform π Z H).subschemeι.base y ∈
        Set.range (Blowup.strictTransform π Z H).subschemeι.base := Set.mem_range_self y
    rwa [Scheme.IdealSheafData.range_subschemeι] at hr
  have h1 : (⟨_, hxB⟩ : ↥B.domain) ∈ ((Blowup.strictTransform π Z H).comap B.domain.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hxsupp
  rw [← restrictIdeal_eq_comap_ι, htop, Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨_, hxB⟩ : ↥B.domain) ∈ ((⊥ : TopologicalSpace.Closeds ↥B.domain) : Set ↥B.domain) :=
    h1
  simp at h2

end FunctorialResolution.EmbeddedResolution

end
