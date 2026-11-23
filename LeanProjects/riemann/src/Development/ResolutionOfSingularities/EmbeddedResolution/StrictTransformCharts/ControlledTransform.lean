import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {Y : Scheme.{u}}

private theorem mul_ideal_apply {Y' : Scheme.{u}} (F G : Y'.IdealSheafData)
    (U : Y'.affineOpens) : (F * G).ideal U = F.ideal U * G.ideal U := rfl

private theorem pow_ideal_apply {Y' : Scheme.{u}} (F : Y'.IdealSheafData) (n : ℕ)
    (U : Y'.affineOpens) : (F ^ n).ideal U = F.ideal U ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, mul_ideal_apply, ih]

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.pow {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ) :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F ^ n) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hF ⊢
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ n, hxU, pow_mem hf n, ?_⟩
  rw [EmbeddedResolution.pow_ideal_apply, hFU, Ideal.span_singleton_pow]

private theorem le_of_forall_ideal_le {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (H : ∀ U : Y.affineOpens, I.ideal U ≤ J.ideal U) : I ≤ J := H

private theorem mul_ideal_le_mul_ideal {Y : Scheme.{u}} {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) :
    F.ideal W * J.ideal W ≤ F.ideal W * J'.ideal W := h W

private theorem exists_affineOpen_ideal_eq_span_singleton {Y : Scheme.{u}} {F : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (x : Y) :
    ∃ (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens))), x ∈ (W : Y.Opens) ∧
      t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens)) ∧ F.ideal W = Ideal.span {t} := by
  unfold Blowup.IsLocallyGeneratedByNonZeroDivisor at hF
  exact hF x

private theorem exists_pow_mul_mem_of_algebraMap_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) [IsLocalization.Away r S] (I : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) I) : ∃ n : ℕ, r ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers r) (S := S)] at hx
  obtain ⟨w, hy⟩ := hx
  rw [← map_mul] at hy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := Submonoid.powers r) (S := S)).mp hy
  obtain ⟨p, hp⟩ : ∃ p : ℕ, r ^ p = (c : R) := c.2
  obtain ⟨q, hq⟩ : ∃ q : ℕ, r ^ q = (w.2 : R) := w.2.2
  refine ⟨p + q, ?_⟩
  have h2 : r ^ (p + q) * x = (c : R) * (w.1 : R) := by
    rw [pow_add, hp, hq, ← hc]; ring
  rw [h2]
  exact I.mul_mem_left _ w.1.2

private theorem ideal_le_ideal_of_mul_le_mul {Y : Scheme.{u}} {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens)))
    (hFW : F.ideal W = Ideal.span {t}) (ht : t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens))) :
    J.ideal W ≤ J'.ideal W := by
  intro b hb
  have h1 : t * b ∈ F.ideal W * J.ideal W := by
    rw [hFW]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hb
  have h2 : t * b ∈ F.ideal W * J'.ideal W := mul_ideal_le_mul_ideal h W h1
  rw [hFW, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨j, hj, hje⟩ := h2
  have h3 : (b - j) * t = 0 := by
    rw [sub_mul, mul_comm b t, mul_comm j t, hje, sub_self]
  have h4 : b = j := eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp ht).2 (b - j) h3)
  rw [h4]
  exact hj

private theorem span_eq_top_of_forall_exists_mem_basicOpen {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(Y, U))
    (h : ∀ x : Y, x ∈ U → ∃ f : s, x ∈ Y.basicOpen (f : Γ(Y, U))) :
    Ideal.span s = ⊤ := by
  rw [← IsAffineOpen.self_le_iSup_basicOpen_iff hU]
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (h x hx)

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul {F J J' : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * J ≤ F * J') : J ≤ J' := by
  refine EmbeddedResolution.le_of_forall_ideal_le fun U => ?_
  intro b hb
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hcover :
      Ideal.span {g : Γ(Y, (U : Y.Opens)) | ∃ n : ℕ, g ^ n * b ∈ J'.ideal U} = ⊤ := by
    refine EmbeddedResolution.span_eq_top_of_forall_exists_mem_basicOpen hU _ ?_
    intro x hx
    obtain ⟨V, t, hxV, htz, hFt⟩ := EmbeddedResolution.exists_affineOpen_ideal_eq_span_singleton hF x
    have hxUV : x ∈ (U : Y.Opens) ⊓ (V : Y.Opens) := ⟨hx, hxV⟩
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU V.2 x hxUV
    have hWfg : Y.affineBasicOpen f = Y.affineBasicOpen g := Subtype.ext hfg
    have hcan : J.ideal (Y.affineBasicOpen f) ≤ J'.ideal (Y.affineBasicOpen f) := by
      rw [hWfg]
      refine EmbeddedResolution.ideal_le_ideal_of_mul_le_mul h (Y.affineBasicOpen g)
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom t) ?_ ?_
      · rw [← F.map_ideal_basicOpen V g, hFt, Ideal.map_span, Set.image_singleton]
        rfl
      · have := V.2.isLocalization_basicOpen g
        exact IsLocalization.nonZeroDivisors_le_comap (.powers g) Γ(Y, Y.basicOpen g) htz
    have hbW : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ J.ideal (Y.affineBasicOpen f) := by
      rw [← J.map_ideal_basicOpen U f]
      exact Ideal.mem_map_of_mem _ hb
    have hbW2 : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J'.ideal U) := by
      have hbW3 := hcan hbW
      rwa [← J'.map_ideal_basicOpen U f] at hbW3
    have := hU.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ :=
      EmbeddedResolution.exists_pow_mul_mem_of_algebraMap_mem_map (S := Γ(Y, Y.basicOpen f)) f (J'.ideal U) b hbW2
    exact ⟨⟨f, n, hn⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J'.ideal U) _ hcover b ?_
  intro r
  have hr : ∃ n : ℕ, (r : Γ(Y, (U : Y.Opens))) ^ n * b ∈ J'.ideal U := r.2
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul {F J J' : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * J = F * J') : J = J' :=
  le_antisymm (hF.le_of_mul_le_mul (le_of_eq h)) (hF.le_of_mul_le_mul (le_of_eq h.symm))

private theorem exists_affineOpen_mem_subset (Z : Scheme.{u}) (x : Z) (W : Z.Opens)
    (hx : x ∈ W) : ∃ V : Z.affineOpens, x ∈ (V : Z.Opens) ∧ (V : Z.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

private theorem coe_image_of_isOpenImmersion {X' Y' : Scheme.{u}} (f : X' ⟶ Y')
    [IsOpenImmersion f] (V : X'.Opens) :
    ((f ''ᵁ V : Y'.Opens) : Set Y') = f.base '' (V : Set X') := rfl

private theorem coe_preimage_opens {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (V : Y'.Opens) :
    ((f ⁻¹ᵁ V : X'.Opens) : Set X') = f.base ⁻¹' (V : Set Y') := rfl

private theorem range_opensι {Y' : Scheme.{u}} (U : Y'.Opens) :
    Set.range U.ι.base = (U : Set Y') := U.range_ι

private theorem image_opensι_le {Y' : Scheme.{u}} (U : Y'.Opens) (V : U.toScheme.Opens) :
    (U.ι ''ᵁ V : Y'.Opens) ≤ U := by
  intro z hz
  have hz' : z ∈ U.ι.base '' (V : Set U.toScheme) := hz
  obtain ⟨w, -, rfl⟩ := hz'
  have hr : U.ι.base w ∈ Set.range U.ι.base := Set.mem_range_self w
  rw [range_opensι] at hr
  exact hr

private theorem image_preimage_opensι {Y' : Scheme.{u}} (U : Y'.Opens) (D : Y'.Opens)
    (hD : D ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
  apply TopologicalSpace.Opens.ext
  rw [coe_image_of_isOpenImmersion, coe_preimage_opens, Set.image_preimage_eq_inter_range,
    range_opensι]
  exact Set.inter_eq_self_of_subset_left hD

private theorem basicOpen_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U : Y'.Opens}
    {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y', U)) :
    X'.basicOpen ((f.appLE U V h).hom r) = V ⊓ f ⁻¹ᵁ (Y'.basicOpen r) := by
  have h1 : (f.appLE U V h).hom r
      = (X'.presheaf.map (homOfLE h).op).hom ((f.app U).hom r) := rfl
  rw [h1, Scheme.basicOpen_res, Scheme.preimage_basicOpen]

private noncomputable def sectionsOpensImageIso {Y' : Scheme.{u}} (U : Y'.Opens)
    (V : U.toScheme.Opens) : Γ(Y', U.ι ''ᵁ V) ≅ Γ(U.toScheme, V) := U.ι.appIso V

private theorem restrictAppIso_hom {Y' : Scheme.{u}} (U : Y'.Opens) (V : U.toScheme.Opens) :
    (sectionsOpensImageIso U V).hom
      = U.ι.appLE (U.ι ''ᵁ V) V (U.ι.preimage_image_eq V).ge :=
  Scheme.Hom.appIso_hom' U.ι V

private theorem map_comp_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U₁ U₂ : Y'.Opens}
    (e : U₁ ≤ U₂) {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U₁) (h' : V ≤ f ⁻¹ᵁ U₂) :
    Y'.presheaf.map (homOfLE e).op ≫ f.appLE U₁ V h = f.appLE U₂ V h' :=
  Scheme.Hom.map_appLE f h (homOfLE e).op

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_opensι {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    (U : Y.Opens) : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F.comap U.ι) := by
  intro x
  obtain ⟨W, t, hyW, ht, hFW⟩ := hF (U.ι.base x)
  obtain ⟨V₀, hxV₀, hV₀⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_subset U.toScheme x (U.ι ⁻¹ᵁ (W : Y.Opens)) hyW
  have hD₀aff : IsAffineOpen (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) :=
    V₀.2.image_of_isOpenImmersion U.ι
  have hyD₀ : U.ι.base x ∈ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := ⟨x, hxV₀, rfl⟩
  obtain ⟨a, b, hab, hya⟩ :=
    exists_basicOpen_le_affine_inter W.2 hD₀aff (U.ι.base x) ⟨hyW, hyD₀⟩
  have hDD₀ : Y.basicOpen a ≤ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := by
    rw [hab]
    exact Y.basicOpen_le b
  have hDU : Y.basicOpen a ≤ U := hDD₀.trans (EmbeddedResolution.image_opensι_le U (V₀ : U.toScheme.Opens))
  have hDW : Y.basicOpen a ≤ (W : Y.Opens) := Y.basicOpen_le a
  have hpreV₀ : U.ι ⁻¹ᵁ (Y.basicOpen a) ≤ (V₀ : U.toScheme.Opens) := by
    intro z hz
    have h2 : z ∈ U.ι ⁻¹ᵁ (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) := hDD₀ hz
    rwa [U.ι.preimage_image_eq] at h2
  have hV₁eq : U.toScheme.basicOpen
      ((U.ι.appLE (W : Y.Opens) (V₀ : U.toScheme.Opens) hV₀).hom a)
      = U.ι ⁻¹ᵁ (Y.basicOpen a) := by
    rw [_root_.FunctorialResolution.EmbeddedResolution.basicOpen_appLE]
    exact inf_eq_right.mpr hpreV₀
  have hV₁aff : IsAffineOpen (U.ι ⁻¹ᵁ (Y.basicOpen a)) := by
    rw [← hV₁eq]
    exact V₀.2.basicOpen _
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a)) = Y.basicOpen a :=
    EmbeddedResolution.image_preimage_opensι U (Y.basicOpen a) hDU
  have himgW : (U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a))) ≤ (W : Y.Opens) := by
    rw [himg]
    exact hDW
  have hleW : (U.ι ⁻¹ᵁ (Y.basicOpen a)) ≤ U.ι ⁻¹ᵁ (W : Y.Opens) := fun z hz => hDW hz
  refine ⟨⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩,
    (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t, hya, ?_, ?_⟩
  · have := W.2.isLocalization_basicOpen a
    have ht' : (Y.presheaf.map (homOfLE hDW).op).hom t
        ∈ nonZeroDivisors Γ(Y, Y.basicOpen a) :=
      IsLocalization.nonZeroDivisors_le_comap (.powers a) Γ(Y, Y.basicOpen a) ht
    have hmor : Y.presheaf.map (homOfLE hDW).op ≫ Y.presheaf.map (eqToHom himg).op ≫
        (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom
        = U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW := by
      rw [EmbeddedResolution.restrictAppIso_hom, ← Category.assoc, ← Functor.map_comp]
      have h3 : eqToHom himg ≫ homOfLE hDW = homOfLE himgW := Subsingleton.elim _ _
      have h3' : (homOfLE hDW).op ≫ (eqToHom himg).op = (homOfLE himgW).op := by
        rw [← op_comp, h3]
      rw [h3']
      exact EmbeddedResolution.map_comp_appLE U.ι himgW _ hleW
    have hfin : (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t
        = (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom.hom
            ((Y.presheaf.map (eqToHom himg).op).hom
              ((Y.presheaf.map (homOfLE hDW).op).hom t)) := by
      rw [← hmor]
      rfl
    rw [hfin]
    exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso
      (Y.presheaf.mapIso (eqToIso himg).op ≪≫ _root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))) ht'
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE F U.ι W
      ⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩ hleW, hFW, Ideal.map_span, Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul_comap_opensι {F : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y.Opens) {J J' : U.toScheme.IdealSheafData}
    (h : F.comap U.ι * J = F.comap U.ι * J') : J = J' :=
  (hF.comap_opensι U).eq_of_mul_eq_mul h

private theorem mem_colon_span {R : Type*} [CommRing R] (I : Ideal R) (s : Set R)
    (x : R) (h : ∀ g ∈ s, x * g ∈ I) : x ∈ I.colon (Submodule.span R s) := by
  refine Submodule.mem_colon.2 ?_
  intro p hp
  rw [smul_eq_mul]
  induction hp using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => rw [mul_zero]; exact zero_mem I
  | add y z _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul c y _ ih =>
    rw [smul_eq_mul, ← mul_assoc, mul_comm x c, mul_assoc]
    exact I.mul_mem_left c ih

private theorem map_colon_eq_colon_map_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (I J : Ideal R) (hJ : J.FG) :
    Ideal.map (algebraMap R S) (I.colon J) =
      (Ideal.map (algebraMap R S) I).colon (Ideal.map (algebraMap R S) J) := by
  refine le_antisymm ?_ ?_
  · have hsub : Ideal.map (algebraMap R S) (I.colon J) * Ideal.map (algebraMap R S) J ≤
        Ideal.map (algebraMap R S) I := by
      rw [← Ideal.map_mul]
      refine Ideal.map_mono (Ideal.mul_le.2 ?_)
      intro a ha b hb
      have ha' := Submodule.mem_colon.mp ha b hb
      rwa [smul_eq_mul] at ha'
    intro z hz
    refine Submodule.mem_colon.2 ?_
    intro p hp
    rw [smul_eq_mul]
    exact hsub (Ideal.mul_mem_mul hz hp)
  · intro b hb
    obtain ⟨s, hs⟩ := hJ
    obtain ⟨w, hab⟩ := IsLocalization.surj (M := Submonoid.powers r) b
    have key : ∀ g ∈ (s : Set R), ∃ n : ℕ, r ^ n * (w.1 * g) ∈ I := by
      intro g hg
      have hgJ : g ∈ J := by
        rw [← hs]; exact Submodule.subset_span hg
      have h1 := Submodule.mem_colon.mp hb (algebraMap R S g) (Ideal.mem_map_of_mem _ hgJ)
      rw [smul_eq_mul] at h1
      have h2 : algebraMap R S (w.1 * g) ∈ Ideal.map (algebraMap R S) I := by
        have heq : algebraMap R S (w.1 * g) =
            b * algebraMap R S g * algebraMap R S (w.2 : R) := by
          rw [map_mul, ← hab]; ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ h1
      exact exists_pow_mul_mem_of_algebraMap_mem_map r I (w.1 * g) h2
    choose! n hn using key
    have hNa : r ^ (s.sup n) * w.1 ∈ I.colon J := by
      rw [← hs]
      refine mem_colon_span I (↑s) (r ^ (s.sup n) * w.1) ?_
      intro g hg
      have hle : n g ≤ s.sup n := Finset.le_sup (Finset.mem_coe.mp hg)
      have hg' := hn g hg
      have hpow : r ^ (s.sup n - n g) * r ^ (n g) = r ^ (s.sup n) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hre : r ^ (s.sup n) * w.1 * g = r ^ (s.sup n - n g) * (r ^ (n g) * (w.1 * g)) := by
        rw [← hpow]; ring
      rw [hre]
      exact I.mul_mem_left _ hg'
    have hmem : r ^ (s.sup n) * (w.2 : R) ∈ Submonoid.powers r :=
      mul_mem (pow_mem (Submonoid.mem_powers r) _) w.2.2
    have hunit : IsUnit (algebraMap R S (r ^ (s.sup n) * (w.2 : R))) :=
      IsLocalization.map_units (M := Submonoid.powers r) S
        ⟨r ^ (s.sup n) * (w.2 : R), hmem⟩
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have hb2 : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) ∈
        Ideal.map (algebraMap R S) (I.colon J) := by
      have heq : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) =
          algebraMap R S (r ^ (s.sup n) * w.1) := by
        rw [map_mul, map_mul, ← hab]; ring
      rw [heq]
      exact Ideal.mem_map_of_mem _ hNa
    have hbv := Ideal.mul_mem_right v (Ideal.map (algebraMap R S) (I.colon J)) hb2
    rw [mul_assoc, hv, mul_one] at hbv
    exact hbv

theorem idealSheafColon_ideal_map_basicOpen [IsLocallyNoetherian Y]
    (I' F : Y.IdealSheafData) (U : Y.affineOpens) (f : Γ(Y, U)) :
    Ideal.map (CommRingCat.Hom.hom (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op))
        ((I'.ideal U).colon (F.ideal U)) =
      (I'.ideal (Y.affineBasicOpen f)).colon (F.ideal (Y.affineBasicOpen f)) := by
  have := IsLocallyNoetherian.component_noetherian U
  have : IsLocalization.Away f Γ(Y, Y.basicOpen f) := U.2.isLocalization_basicOpen f
  have key := map_colon_eq_colon_map_away (S := Γ(Y, Y.basicOpen f)) f (I'.ideal U) (F.ideal U)
    (IsNoetherian.noetherian (F.ideal U))
  rw [← I'.map_ideal_basicOpen U f, ← F.map_ideal_basicOpen U f]
  exact key

def idealSheafColon [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := (I'.ideal U).colon (F.ideal U)
  map_ideal_basicOpen := idealSheafColon_ideal_map_basicOpen I' F

@[simp]
theorem idealSheafColon_ideal [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData)
    (U : Y.affineOpens) :
    (idealSheafColon I' F).ideal U = (I'.ideal U).colon (F.ideal U) :=
  rfl

private theorem span_singleton_mul_colon {R : Type*} [CommRing R] {P J : Ideal R}
    (hP : ∃ f : R, P = Ideal.span {f}) (hJ : J ≤ P) : P * J.colon P = J := by
  obtain ⟨f, rfl⟩ := hP
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hJ hy)
    have hc : c ∈ J.colon (Ideal.span {f}) := by
      refine Submodule.mem_colon.2 ?_
      intro p hp
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [smul_eq_mul]
      have hre : c * (d * f) = d * (c * f) := by ring
      rw [hre]
      exact J.mul_mem_left d hy
    have hmem := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hc
    rwa [mul_comm f c] at hmem

private theorem exists_ideal_eq_span_singleton_congr {Y' : Scheme.{u}} (F : Y'.IdealSheafData)
    {W W' : Y'.affineOpens} (hW : W = W')
    (h : ∃ f : Γ(Y', W'), F.ideal W' = Ideal.span {f}) :
    ∃ f : Γ(Y', W), F.ideal W = Ideal.span {f} := by
  subst hW
  exact h

private theorem exists_basicOpen_ideal_eq_span_singleton {Y' : Scheme.{u}} (F : Y'.IdealSheafData)
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y'.affineOpens) (y : Y')
    (hy : y ∈ (U : Y'.Opens)) :
    ∃ g : Γ(Y', U), y ∈ Y'.basicOpen g ∧
      ∃ f : Γ(Y', Y'.affineBasicOpen g), F.ideal (Y'.affineBasicOpen g) = Ideal.span {f} := by
  obtain ⟨V, fV, hyV, hfV, hFV⟩ := hF y
  obtain ⟨g, h, heq, hyg⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
  refine ⟨g, hyg, ?_⟩
  have habo : Y'.affineBasicOpen g = Y'.affineBasicOpen h := Subtype.ext heq
  refine exists_ideal_eq_span_singleton_congr F habo ?_
  have hmap := F.map_ideal_basicOpen V h
  rw [hFV, Ideal.map_span, Set.image_singleton] at hmap
  exact ⟨_, hmap.symm⟩

private theorem span_eq_top_of_cover_basicOpen {Y' : Scheme.{u}} (U : Y'.affineOpens)
    (T : Set Γ(Y', U))
    (hcov : ∀ y : Y', y ∈ (U : Y'.Opens) → ∃ g ∈ T, y ∈ Y'.basicOpen g) :
    Ideal.span T = ⊤ := by
  refine span_eq_top_of_forall_exists_mem_basicOpen U.2 T ?_
  intro y hy
  obtain ⟨g, hgT, hyg⟩ := hcov y hy
  exact ⟨⟨g, hgT⟩, hyg⟩

private theorem exists_pow_mul_mem_mul_colon {Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (F I' : Y'.IdealSheafData) (hIle : ∀ U : Y'.affineOpens, I'.ideal U ≤ F.ideal U)
    (U : Y'.affineOpens) (x : Γ(Y', U)) (hx : x ∈ I'.ideal U) (g : Γ(Y', U))
    (f : Γ(Y', Y'.affineBasicOpen g))
    (hf : F.ideal (Y'.affineBasicOpen g) = Ideal.span {f}) :
    ∃ n : ℕ, g ^ n * x ∈ F.ideal U * (I'.ideal U).colon (F.ideal U) := by
  have : IsLocalization.Away g Γ(Y', Y'.basicOpen g) := U.2.isLocalization_basicOpen g
  have h1 : Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
      (F.ideal U * (I'.ideal U).colon (F.ideal U)) = I'.ideal (Y'.affineBasicOpen g) := by
    rw [Ideal.map_mul, F.map_ideal_basicOpen U g,
      idealSheafColon_ideal_map_basicOpen I' F U g]
    exact span_singleton_mul_colon ⟨f, hf⟩ (hIle (Y'.affineBasicOpen g))
  have h2 : (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := by
    rw [h1, ← I'.map_ideal_basicOpen U g]
    exact Ideal.mem_map_of_mem _ hx
  have h3 : algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g) x ∈
      Ideal.map (algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := h2
  exact exists_pow_mul_mem_of_algebraMap_mem_map g _ x h3

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.mul_idealSheafColon [IsLocallyNoetherian Y]
    {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    F * EmbeddedResolution.idealSheafColon I' F = I' := by
  have hIle : ∀ U : Y.affineOpens, I'.ideal U ≤ F.ideal U := fun U => hI U
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [EmbeddedResolution.mul_ideal_apply, EmbeddedResolution.idealSheafColon_ideal]
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro x hx
    have hspan : Ideal.span {g : Γ(Y, U) | ∃ f : Γ(Y, Y.affineBasicOpen g),
        F.ideal (Y.affineBasicOpen g) = Ideal.span {f}} = ⊤ := by
      refine EmbeddedResolution.span_eq_top_of_cover_basicOpen U _ ?_
      intro y hy
      obtain ⟨g, hyg, hfg⟩ := EmbeddedResolution.exists_basicOpen_ideal_eq_span_singleton F hF U y hy
      exact ⟨g, hfg, hyg⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan x ?_
    intro r
    have hr : ∃ f : Γ(Y, Y.affineBasicOpen (r : Γ(Y, U))),
        F.ideal (Y.affineBasicOpen (r : Γ(Y, U))) = Ideal.span {f} := r.2
    obtain ⟨f, hf⟩ := hr
    obtain ⟨n, hn⟩ := EmbeddedResolution.exists_pow_mul_mem_mul_colon F I' hIle U x hx (r : Γ(Y, U)) f hf
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq [IsLocallyNoetherian Y]
    {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    ∃ J : Y.IdealSheafData, F * J = I' :=
  ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.existsUnique_mul_eq [IsLocallyNoetherian Y]
    {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    ∃! J : Y.IdealSheafData, F * J = I' := by
  refine ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI, ?_⟩
  intro J hJ
  exact hF.eq_of_mul_eq_mul (hJ.trans (hF.mul_idealSheafColon hI).symm)

variable {X X₁ : Scheme.{u}}

theorem comap_le_exceptionalIdeal_pow (π : X₁ ⟶ X) {Z I : X.IdealSheafData} {n : ℕ}
    (hI : I ≤ Z ^ n) : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := by
  rw [Blowup.exceptionalIdeal_eq_comap, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
  apply AlgebraicGeometry.Scheme.IdealSheafData.comap_mono
  exact hI

theorem existsUnique_pow_mul_eq_comap [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z))
    (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π :=
  (hZ.pow n).existsUnique_mul_eq (comap_le_exceptionalIdeal_pow π hI)

theorem existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π := by
  have hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact existsUnique_pow_mul_eq_comap π Z I n hZ hI

def controlledTransform [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z I : X.IdealSheafData)
    (n : ℕ) (_hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (_hI : I ≤ Z ^ n) : X₁.IdealSheafData :=
  idealSheafColon (I.comap π) (Blowup.exceptionalIdeal π Z ^ n)

theorem exceptionalIdeal_pow_mul_controlledTransform [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n) :
    Blowup.exceptionalIdeal π Z ^ n * controlledTransform π Z I n hπ hI = I.comap π := by
  have hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  have hle : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := comap_le_exceptionalIdeal_pow π hI
  exact (hZ.pow n).mul_idealSheafColon hle

theorem eq_controlledTransform_of_mul_eq_comap [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n)
    (J : X₁.IdealSheafData) (hJ : Blowup.exceptionalIdeal π Z ^ n * J = I.comap π) :
    J = controlledTransform π Z I n hπ hI :=
  (existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z I n hπ hI).unique hJ
    (exceptionalIdeal_pow_mul_controlledTransform π Z I n hπ hI)

end FunctorialResolution.EmbeddedResolution

end
