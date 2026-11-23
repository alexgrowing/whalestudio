import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.Blowup

universe u

def sectionsRingHom {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) : A →+* ↥Γ(W, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom

theorem sectionsRingHom_apply {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (r : A) :
    sectionsRingHom g V r =
      (g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) := rfl

theorem sectionsRingHom_restrict {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) {V V' : W.Opens} (hV : V' ≤ V) (r : A) :
    sectionsRingHom g V' r =
      (W.presheaf.map (homOfLE hV).op).hom (sectionsRingHom g V r) := by
  have hmap : W.presheaf.map
        (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
      = W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op ≫
        W.presheaf.map (homOfLE hV).op :=
    W.presheaf.map_comp
      (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op
      (homOfLE hV).op
  have key : g.appLE ⊤ V' (le_top.trans (Scheme.Hom.preimage_top g).ge) =
      g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge) ≫
        W.presheaf.map (homOfLE hV).op := by
    show g.app ⊤ ≫ W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
        = (g.app ⊤ ≫ W.presheaf.map
            (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op) ≫
          W.presheaf.map (homOfLE hV).op
    rw [Category.assoc, ← hmap]
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) ⟶ Γ(W, V') =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)) key

theorem comap_specIdealSheaf_ideal {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    ((specIdealSheaf I).comap g).ideal V = Ideal.map (sectionsRingHom g (V : W.Opens)) I := by
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) g
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ V
      (le_top.trans (Scheme.Hom.preimage_top g).ge)
  rw [specIdealSheaf_ideal_top, Ideal.map_map] at h1
  exact h1

private theorem localization_mk_one_pow {A : Type u} [CommRing A] (S : Submonoid A) (x : A)
    (n : ℕ) :
    Localization.mk x (1 : S) ^ n = Localization.mk (x ^ n) (1 : S) := by
  rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap, map_pow]

private theorem val_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I) (r : R) :
    (chartRingHom I a r).val =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesGrading I 0)) : ↥(reesAlgebra I))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := by
  rw [chartRingHom_apply]
  rfl

theorem exists_mul_pow_eq_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by
  obtain ⟨k, hk⟩ := z.den_mem
  obtain ⟨s, hs, hnum⟩ := (mem_reesGrading_iff_monomial I z.deg z.num).mp z.num_mem_deg
  have hdencoe : ((z.den : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial k ((a : R) ^ k) := by
    rw [← hk]
    simp [reesGenerator_coe, Polynomial.monomial_pow]
  by_cases hik : z.deg = k
  · refine ⟨k, s, ?_⟩
    apply HomogeneousLocalization.val_injective
    have key : z.num * ((reesDegreeZeroEquiv I (a : R) : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) ^ k
        = z.den * ((reesDegreeZeroEquiv I s : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      push_cast
      rw [hnum, hdencoe, hik, reesDegreeZeroEquiv_coe_coe, reesDegreeZeroEquiv_coe_coe,
        ← Polynomial.C_pow, ← Polynomial.monomial_zero_left, ← Polynomial.monomial_zero_left,
        Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial, mul_comm]
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simpa using key⟩
  · refine ⟨0, 0, ?_⟩
    apply HomogeneousLocalization.val_injective
    have hak : (a : R) ^ k = 0 := by
      have h0 := (mem_reesGrading_iff_coeff I z.deg z.den).mp z.den_mem_deg k (Ne.symm hik)
      rw [hdencoe] at h0
      simpa using h0
    have hden0 : (z.den : ↥(reesAlgebra I)) = 0 := by
      apply Subtype.ext
      rw [hdencoe, hak]
      simp
    have h0S : (0 : ↥(reesAlgebra I)) ∈ Submonoid.powers (reesGenerator I a) := ⟨k, hk.trans hden0⟩
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨⟨0, h0S⟩, by simp [hden0]⟩

def chartSectionsRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b) →+* ↥Γ(W, V) :=
  ((chartSectionsIso I b).hom ≫ h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom

theorem chartSectionsRingHom_apply {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b)) :
    chartSectionsRingHom I h b V hV z =
      (h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom ((chartSectionsIso I b).hom.hom z) :=
  rfl

theorem chartSectionsRingHom_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) (r : R) :
    chartSectionsRingHom I h b V hV (chartRingHom I b r) =
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  have key : CommRingCat.ofHom (chartRingHom I b) ≫ ((chartSectionsIso I b).hom ≫
        h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV)
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (h ≫ AffineBlowup.toSpec I).appLE ⊤ V
          (le_top.trans (Scheme.Hom.preimage_top (h ≫ AffineBlowup.toSpec I)).ge) := by
    rw [← Category.assoc, chartRingHom_comp_chartSectionsIso_hom, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : CommRingCat.of R ⟶ Γ(W, V) => φ.hom r) key

theorem comap_specIdealSheaf_ideal_eq_span {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I) (a : ↥I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
      Ideal.span
        {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
  have hfac : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)
      = RingHom.comp (chartSectionsRingHom I h a (V : W.Opens) hV) (chartRingHom I a) := by
    ext r
    exact (chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV r).symm
  have h2 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)) I
      = Ideal.span
          {chartSectionsRingHom I h a (V : W.Opens) hV (chartRingHom I a (a : R))} := by
    rw [hfac, ← Ideal.map_map, map_chartRingHom_eq_span_singleton I a, Ideal.map_span, Set.image_singleton]
  rw [comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) V, h2,
    chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV (a : R)]

private theorem mem_nonZeroDivisors_of_span_singleton_eq {B : Type u} [CommRing B] {s t : B}
    (hs : s ∈ nonZeroDivisors B)
    (hst : Ideal.span ({s} : Set B) = Ideal.span ({t} : Set B)) :
    t ∈ nonZeroDivisors B := by
  obtain ⟨hs1, hs2⟩ := mem_nonZeroDivisors_iff.mp hs
  have h1 : t ∈ Ideal.span ({s} : Set B) := by
    rw [hst]; exact Ideal.mem_span_singleton_self t
  have h2 : s ∈ Ideal.span ({t} : Set B) := by
    rw [← hst]; exact Ideal.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : v * (u * s) = s := by rw [hu, hv]
  have hss : s * (1 - v * u) = 0 := by linear_combination -h3
  have h4 : (1 : B) - v * u = 0 := hs1 _ hss
  have hvu : v * u = 1 := by linear_combination -h4
  have key : ∀ y : B, t * y = 0 → y = 0 := by
    intro y hy
    have h5 : s * (u * y) = 0 := by linear_combination hy + y * hu
    have h6 : u * y = 0 := hs1 _ h5
    linear_combination v * h6 - y * hvu
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

private theorem map_sectionsRingHom_restrict {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) {V V' : W.Opens} (hV : V' ≤ V) :
    Ideal.map (sectionsRingHom g V') I
      = Ideal.map (W.presheaf.map (homOfLE hV).op).hom (Ideal.map (sectionsRingHom g V) I) := by
  have e : (W.presheaf.map (homOfLE hV).op).hom.comp (sectionsRingHom g V) = sectionsRingHom g V' :=
    RingHom.ext fun x => (sectionsRingHom_restrict g hV x).symm
  rw [Ideal.map_map, e]

private theorem exists_mem_opensRange_affineBlowupChart {R : Type u} [CommRing R] (I : Ideal R)
    (p : ↥(affineBlowup I)) :
    ∃ c : ↥I, p ∈ (affineBlowupChart I c).opensRange := by
  have hcov : (⨆ c : ↥I, (affineBlowupChart I c).opensRange) = ⊤ := by
    simp only [opensRange_affineBlowupChart_eq_basicOpen]
    exact iSup_proj_basicOpen_reesGenerator_eq_top I
  have hp : p ∈ (⨆ c : ↥I, (affineBlowupChart I c).opensRange) := by
    rw [hcov]; trivial
  simpa using hp

private theorem restrict_basicOpen_mem_nonZeroDivisors {W : Scheme.{u}} {U : W.Opens}
    (hU : IsAffineOpen U) (r : ↥Γ(W, U)) {s : ↥Γ(W, U)} (hs : s ∈ nonZeroDivisors ↥Γ(W, U))
    (hle : W.basicOpen r ≤ U) :
    (W.presheaf.map (homOfLE hle).op).hom s ∈ nonZeroDivisors ↥Γ(W, W.basicOpen r) := by
  have := hU.isLocalization_basicOpen r
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r)
    ↥Γ(W, W.basicOpen r) hs

private theorem isLocalizationElem_eq_chartFraction {R : Type u} [CommRing R] (I : Ideal R)
    (c a : ↥I) :
    HomogeneousLocalization.Away.isLocalizationElem
        (reesGenerator_mem_reesGrading I c) (reesGenerator_mem_reesGrading I a)
      = chartFraction I c a := by
  apply HomogeneousLocalization.val_injective
  rw [chartFraction_eq_mk]
  simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.val_mk, pow_one]

private theorem affineBlowupChart_preimage_basicOpen {R : Type u} [CommRing R] (I : Ideal R)
    (c : ↥I) (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    affineBlowupChart I c ⁻¹ᵁ
        ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z))
      = PrimeSpectrum.basicOpen z := by
  have e : (⊤ : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).Opens)
      ≤ affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) := by
    intro x _
    exact ⟨x, trivial, rfl⟩
  have happ : (affineBlowupChart I c).appLE (affineBlowupChart I c ''ᵁ ⊤) ⊤ e
      = ((affineBlowupChart I c).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom]
    rfl
  have hiso : (((affineBlowupChart I c).appIso ⊤).hom).hom ((chartSectionsIso I c).hom.hom z)
      = (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z := by
    rw [chartSectionsIso_hom_apply]
    exact congrArg
      (fun φ : Γ(Spec (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))), ⊤) ⟶
          Γ(Spec (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))), ⊤) =>
        φ.hom ((Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z))
      ((affineBlowupChart I c).appIso ⊤).inv_hom_id
  have h2 : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z)
      = PrimeSpectrum.basicOpen z :=
    basicOpen_eq_of_affine
      (R := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))) z
  have h1 : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).basicOpen
        (((affineBlowupChart I c).appLE (affineBlowupChart I c ''ᵁ ⊤) ⊤ e).hom
          ((chartSectionsIso I c).hom.hom z))
      = ⊤ ⊓ affineBlowupChart I c ⁻¹ᵁ
          ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z)) :=
    Scheme.basicOpen_appLE (affineBlowupChart I c) ⊤ (affineBlowupChart I c ''ᵁ ⊤) e
      ((chartSectionsIso I c).hom.hom z)
  rw [happ, hiso, h2, top_inf_eq] at h1
  exact h1.symm

private theorem basicOpen_chartFraction_le_opensRange {R : Type u} [CommRing R] (I : Ideal R)
    (c a : ↥I) :
    (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))
      ≤ (affineBlowupChart I a).opensRange := by
  have hpre : affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I a).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I c a) := by
    rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι, ← isLocalizationElem_eq_chartFraction I c a]
    exact Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I c) Nat.one_pos
      (reesGenerator_mem_reesGrading I a) Nat.one_pos
  intro p hp
  have hsub : (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))
      ≤ affineBlowupChart I c ''ᵁ ⊤ := Scheme.basicOpen_le _ _
  obtain ⟨q, -, hq⟩ := hsub hp
  rw [← hq] at hp
  have hq2 : q ∈ affineBlowupChart I c ⁻¹ᵁ
      ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))) := hp
  rw [affineBlowupChart_preimage_basicOpen, ← hpre] at hq2
  rw [← hq]
  exact hq2

private theorem basicOpen_chartSectionsRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (c : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    W.basicOpen (chartSectionsRingHom I h c V hV z)
      = V ⊓ h ⁻¹ᵁ ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z)) := by
  rw [chartSectionsRingHom_apply]
  exact Scheme.basicOpen_appLE h V (affineBlowupChart I c ''ᵁ ⊤) hV
    ((chartSectionsIso I c).hom.hom z)

private theorem mem_opensRange_of_mem_basicOpen_chartSectionsRingHom {R : Type u} [CommRing R]
    (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I) (c a : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤)) {w : ↥W}
    (hw : w ∈ W.basicOpen (chartSectionsRingHom I h c V hV (chartFraction I c a))) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by
  rw [basicOpen_chartSectionsRingHom I h c V hV (chartFraction I c a)] at hw
  have hw2 : h.base w ∈
      (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a)) := hw.2
  exact basicOpen_chartFraction_le_opensRange I c a hw2

theorem mem_opensRange_affineBlowupChart_of_ideal_eq_span {R : Type u} [CommRing R]
    (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) (a : ↥I)
    (hex : ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧
      ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
        Ideal.span
          {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by
  obtain ⟨V, hwV, hVspan⟩ := hex
  obtain ⟨c, hc⟩ := exists_mem_opensRange_affineBlowupChart I (h.base w)
  obtain ⟨Uaff, g, hwU, hgnzd, hUspan⟩ := hcart w
  have hwpre : w ∈ ((V : W.Opens) ⊓ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) : W.Opens) := by
    refine ⟨hwV, ?_⟩
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hc
  obtain ⟨r, hrle, hwr⟩ := Uaff.2.exists_basicOpen_le
    (⟨w, hwpre⟩ : ↥((V : W.Opens) ⊓ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) : W.Opens)) hwU
  have hbaff : IsAffineOpen (W.basicOpen r) := Uaff.2.basicOpen r
  have hVV : W.basicOpen r ≤ (V : W.Opens) := le_trans hrle inf_le_left
  have hVc : W.basicOpen r ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) := le_trans hrle inf_le_right
  have hVU : W.basicOpen r ≤ (Uaff : W.Opens) := W.basicOpen_le r
  have hmapSpan : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)} := by
    have e1 := comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I)
      (⟨W.basicOpen r, hbaff⟩ : W.affineOpens)
    have e2 := comap_specIdealSheaf_ideal_eq_span I h c
      (⟨W.basicOpen r, hbaff⟩ : W.affineOpens) hVc
    exact e1.symm.trans e2
  have hmapPow : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)} := by
    have e1 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)) I
        = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} :=
      (comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) V).symm.trans hVspan
    rw [map_sectionsRingHom_restrict I (h ≫ AffineBlowup.toSpec I) hVV, e1, Ideal.map_span,
      Set.image_singleton, ← sectionsRingHom_restrict (h ≫ AffineBlowup.toSpec I) hVV (a : R)]
  have hmapEq : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {(W.presheaf.map (homOfLE hVU).op).hom g} := by
    have e1 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (Uaff : W.Opens)) I
        = Ideal.span {g} :=
      (comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) Uaff).symm.trans hUspan
    rw [map_sectionsRingHom_restrict I (h ≫ AffineBlowup.toSpec I) hVU, e1, Ideal.map_span,
      Set.image_singleton]
  have hcnzd : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen r) :=
    mem_nonZeroDivisors_of_span_singleton_eq (restrict_basicOpen_mem_nonZeroDivisors Uaff.2 r hgnzd hVU)
      (hmapEq.symm.trans hmapSpan)
  have hkey : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)
      = chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a) *
        sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R) := by
    rw [← chartSectionsRingHom_chartRingHom I h c (W.basicOpen r) hVc (a : R),
      ← chartSectionsRingHom_chartRingHom I h c (W.basicOpen r) hVc (c : R), ← map_mul,
      chartRingHom_coe_eq_chartFraction_mul I c a]
  have hcmem : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)
      ∈ Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)} := by
    rw [← hmapPow]
    exact Ideal.mem_map_of_mem _ c.2
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hcmem
  have hnz := mem_nonZeroDivisors_iff.mp hcnzd
  have h1 : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R) *
      (1 - d * chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) = 0 := by
    linear_combination -hd + d * hkey
  have h2 : (1 : ↥Γ(W, W.basicOpen r)) -
      d * chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a) = 0 := hnz.1 _ h1
  have hunit : IsUnit (chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) :=
    ⟨⟨chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a), d,
      by linear_combination -h2, by linear_combination -h2⟩, rfl⟩
  have hmem : w ∈ W.basicOpen (chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) := by
    rw [W.basicOpen_of_isUnit hunit]
    exact hwr
  exact mem_opensRange_of_mem_basicOpen_chartSectionsRingHom I h c a (W.basicOpen r) hVc hmem

private theorem mem_preimage_affineBlowupChart_iff {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (a : ↥I) (w : ↥W) :
    w ∈ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ↔
      ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧
        ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
          Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
  constructor
  · intro hw
    have hw' : w ∈ ((h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) : W.Opens) : Set ↥W) := hw
    obtain ⟨v, hv, hwV, hVle⟩ :=
      (W.isBasis_affineOpens).exists_subset_of_mem_open hw'
        (TopologicalSpace.Opens.isOpen (h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)))
    obtain ⟨V, hVmem, rfl⟩ := hv
    have hle : ((⟨V, hVmem⟩ : W.affineOpens) : W.Opens)
        ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := SetLike.coe_subset_coe.mp hVle
    exact ⟨⟨V, hVmem⟩, hwV, comap_specIdealSheaf_ideal_eq_span I h a ⟨V, hVmem⟩ hle⟩
  · intro hex
    have hmem := mem_opensRange_affineBlowupChart_of_ideal_eq_span I h hcart w a hex
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hmem

theorem preimage_affineBlowupChart_eq_of_toSpec_eq {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}}
    (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I)))
    (a : ↥I) :
    h₁ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) = h₂ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
  have hcart₂ : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₂ ≫ AffineBlowup.toSpec I)) := by
    rw [← he]
    exact hcart
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro w
  have e1 := mem_preimage_affineBlowupChart_iff I h₁ hcart a w
  have e2 := mem_preimage_affineBlowupChart_iff I h₂ hcart₂ a w
  rw [he] at e1
  exact e1.trans e2.symm

theorem exists_chart_affineOpen_mem_nonZeroDivisors {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) :
    ∃ (a : ↥I) (V : W.affineOpens), w ∈ (V : W.Opens) ∧
      (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ∧
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R) ∈
        nonZeroDivisors ↥Γ(W, (V : W.Opens)) := by
  obtain ⟨a, ha⟩ := exists_mem_opensRange_affineBlowupChart I (h.base w)
  have hwU₀ : w ∈ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
    have h1 := ha
    rw [← Scheme.Hom.image_top_eq_opensRange (affineBlowupChart I a)] at h1
    exact h1
  obtain ⟨U, c, hwU, hcnzd, hideal⟩ := hcart w
  have hUaff : IsAffineOpen (U : W.Opens) := U.2
  obtain ⟨t, htle, hwt⟩ :=
    hUaff.exists_basicOpen_le (V := h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) ⟨w, hwU₀⟩ hwU
  have hwt' : w ∈ W.basicOpen t := hwt
  have : IsLocalization.Away t ↥Γ(W, W.basicOpen t) := hUaff.isLocalization_basicOpen t
  have hres : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)
      = RingHom.comp (algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)))
          (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) := by
    ext r
    exact sectionsRingHom_restrict (h ≫ AffineBlowup.toSpec I) (W.basicOpen_le t) r
  have hmapU : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) I
      = Ideal.span {c} := by
    rw [← comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) U]
    exact hideal
  have hmapV : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I
      = Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c} := by
    rw [hres, ← Ideal.map_map, hmapU, Ideal.map_span, Set.image_singleton]
  have e1 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I :=
    comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) ⟨W.basicOpen t, hUaff.basicOpen t⟩
  have e2 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen t, hUaff.basicOpen t⟩ htle
  have hspan : Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c}
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    hmapV.symm.trans (e1.symm.trans e2)
  have hmem2 : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hcnzd' : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers t)
      ↥Γ(W, W.basicOpen t) hcnzd
  have hdnzd : d * sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) := by
    rw [hd]
    exact hcnzd'
  exact ⟨a, ⟨W.basicOpen t, hUaff.basicOpen t⟩, hwt', htle,
    (mul_mem_nonZeroDivisors.mp hdnzd).2⟩

private theorem chartSectionsRingHom_mul_pow_eq {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (a : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) (n : ℕ) (r : R)
    (hnr : z * chartRingHom I a (a : R) ^ n = chartRingHom I a r) :
    chartSectionsRingHom I h a V hV z * sectionsRingHom (h ≫ AffineBlowup.toSpec I) V (a : R) ^ n
      = sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  have hpow : chartSectionsRingHom I h a V hV (chartRingHom I a (a : R) ^ n)
      = chartSectionsRingHom I h a V hV (chartRingHom I a (a : R)) ^ n :=
    map_pow (chartSectionsRingHom I h a V hV) (chartRingHom I a (a : R)) n
  have h0 : chartSectionsRingHom I h a V hV (z * chartRingHom I a (a : R) ^ n)
      = chartSectionsRingHom I h a V hV (chartRingHom I a r) := by rw [hnr]
  rw [map_mul, hpow, chartSectionsRingHom_chartRingHom, chartSectionsRingHom_chartRingHom] at h0
  exact h0

private def openCoverBySpecOfIsAffineOpen {W : Scheme.{u}} (VV : ↥W → W.Opens)
    (hVaff : ∀ w : ↥W, IsAffineOpen (VV w)) (hmem : ∀ w : ↥W, w ∈ VV w) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ↥W (fun w => Spec Γ(W, VV w)) (fun w => (hVaff w).fromSpec)
    (fun x => by
      have hx : x ∈ Set.range ((hVaff x).fromSpec).base := by
        rw [(hVaff x).range_fromSpec]
        exact hmem x
      obtain ⟨y, hy⟩ := hx
      exact ⟨x, y, hy⟩)
    (fun w => inferInstance)

private theorem fromSpec_comp_eq_of_toSpec_eq {R : Type u} [CommRing R] {I : Ideal R}
    {W : Scheme.{u}} (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I)))
    (a : ↥I) (V : W.Opens) (hVaff : IsAffineOpen V)
    (hle : V ≤ h₁ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤))
    (hnzd : sectionsRingHom (h₁ ≫ AffineBlowup.toSpec I) V (a : R) ∈
      nonZeroDivisors ↥Γ(W, V)) :
    hVaff.fromSpec ≫ h₁ = hVaff.fromSpec ≫ h₂ := by
  have hle₂ : V ≤ h₂ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
    rw [← preimage_affineBlowupChart_eq_of_toSpec_eq h₁ h₂ he hcart a]
    exact hle
  have hTaff : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤) :=
    (isAffineOpen_top _).image_of_isOpenImmersion (affineBlowupChart I a)
  have hcp : chartSectionsRingHom I h₁ a V hle = chartSectionsRingHom I h₂ a V hle₂ := by
    refine RingHom.ext fun z => ?_
    obtain ⟨n, r, hnr⟩ := exists_mul_pow_eq_chartRingHom I a z
    have k1 := chartSectionsRingHom_mul_pow_eq I h₁ a V hle z n r hnr
    have k2 := chartSectionsRingHom_mul_pow_eq I h₂ a V hle₂ z n r hnr
    rw [← he] at k2
    exact (mul_cancel_right_mem_nonZeroDivisors (pow_mem hnzd n)).mp (k1.trans k2.symm)
  have hmor : (chartSectionsIso I a).hom ≫ h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
      = (chartSectionsIso I a).hom ≫ h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ :=
    CommRingCat.hom_ext hcp
  have happ : h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
      = h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by
    calc h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
        = (chartSectionsIso I a).inv ≫ (chartSectionsIso I a).hom ≫
            h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (chartSectionsIso I a).inv ≫ (chartSectionsIso I a).hom ≫
            h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by rw [hmor]
      _ = h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have E₁ := IsAffineOpen.SpecMap_appLE_fromSpec h₁ hTaff hVaff hle
  have E₂ := IsAffineOpen.SpecMap_appLE_fromSpec h₂ hTaff hVaff hle₂
  rw [← E₁, ← E₂, happ]

theorem affineBlowup_hom_ext {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}}
    (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I))) :
    h₁ = h₂ := by
  classical
  choose aa VV hmem hle hnzd using exists_chart_affineOpen_mem_nonZeroDivisors I h₁ hcart
  refine (openCoverBySpecOfIsAffineOpen (fun w => (VV w : W.Opens)) (fun w => (VV w).2) hmem).hom_ext
    h₁ h₂ fun w => ?_
  exact fromSpec_comp_eq_of_toSpec_eq h₁ h₂ he hcart (aa w) ((VV w : W.Opens)) (VV w).2
    (hle w) (hnzd w)

end FunctorialResolution.Blowup
