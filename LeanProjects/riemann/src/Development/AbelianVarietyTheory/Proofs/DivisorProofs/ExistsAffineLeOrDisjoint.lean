import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.DenseClosedAffineSubsets

theorem closed_of_dense {V X T D Y : Scheme.{0}} (p : T ⟶ D) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] (e : Y ⟶ T)
    [IsClosedImmersion (e ≫ p)] (v : V ⟶ Y) (hv : v ≫ e = j ≫ ι) :
    IsClosedImmersion (ι ≫ p) := by
  have : IsClosedImmersion e := IsClosedImmersion.of_comp e p
  have hk : e.ker ≤ ι.ker := by
    have h1 : (j ≫ ι).ker = ι.ker := by
      rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← hv]
    exact Scheme.Hom.le_ker_comp v e
  have hl := IsClosedImmersion.lift_fac e ι hk
  have : IsClosedImmersion (IsClosedImmersion.lift e ι hk ≫ e) := by rw [hl]; infer_instance
  have : IsClosedImmersion (IsClosedImmersion.lift e ι hk) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ e
  rw [← hl, Category.assoc]
  infer_instance

instance dominant_restrict {V X : Scheme.{0}} (j : V ⟶ X) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] (O : X.Opens) : IsSchemeTheoreticallyDominant (j ∣_ O) :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict j O).flip

theorem closed_restrict_of_dense {V X T P Y : Scheme.{0}} (p : T ⟶ P) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (D : P.Opens) (y : Y ⟶ D) [IsClosedImmersion y] (e : Y ⟶ T) (he : e ≫ p = y ≫ D.ι)
    (hv : ∀ (Z : Scheme.{0}) (a : Z ⟶ V) (b : Z ⟶ D), a ≫ j ≫ ι ≫ p = b ≫ D.ι →
      ∃ v : Z ⟶ Y, v ≫ e = a ≫ j ≫ ι) :
    IsClosedImmersion ((ι ≫ p) ∣_ D) := by
  have hr : Set.range e ⊆ Set.range (p ⁻¹ᵁ D).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (e z) ∈ D
    rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    exact (y z).2
  let e' : Y ⟶ (p ⁻¹ᵁ D).toScheme := IsOpenImmersion.lift (p ⁻¹ᵁ D).ι e hr
  have he' : e' ≫ (p ⁻¹ᵁ D).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hy : e' ≫ p ∣_ D = y := by
    rw [← cancel_mono D.ι, Category.assoc, morphismRestrict_ι, reassoc_of% he', he]
  have : IsClosedImmersion (e' ≫ p ∣_ D) := by rw [hy]; infer_instance
  obtain ⟨v, hv⟩ := hv _ (j ⁻¹ᵁ ι ⁻¹ᵁ p ⁻¹ᵁ D).ι
    (j ∣_ (ι ⁻¹ᵁ p ⁻¹ᵁ D) ≫ ι ∣_ (p ⁻¹ᵁ D) ≫ p ∣_ D) (by simp)
  have := closed_of_dense (p ∣_ D) (ι ∣_ (p ⁻¹ᵁ D)) (j ∣_ (ι ⁻¹ᵁ p ⁻¹ᵁ D)) e' v (by
    rw [← cancel_mono (p ⁻¹ᵁ D).ι]
    simp [he', hv])
  rw [morphismRestrict_comp]
  exact this

theorem exists_closed_affineSpace {U S : Scheme.{0}} [IsAffine U] [IsAffine S] (u : U ⟶ S)
    [LocallyOfFiniteType u] :
    ∃ (σ : Type) (_ : Fintype σ) (g : σ → Γ(U, ⊤)),
      IsClosedImmersion (AffineSpace.homOfVector u g) := by
  have h : u.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  letI := u.appTop.hom.toAlgebra
  obtain ⟨t, ht⟩ := h.out
  refine ⟨t, inferInstance, fun a ↦ a.1, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin Γ(S, ⊤) (t : Set Γ(U, ⊤)) := ht ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨_, AffineSpace.homOfVector_appTop_coord u (fun a : t ↦ a.1) ⟨x, hx⟩⟩
  | algebraMap r =>
    refine ⟨(𝔸(t; S) ↘ S).appTop r, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

theorem exists_affine_le_or_disjoint {W : Scheme.{0}} [Nonempty W] (t : Finset W.Opens) :
    ∃ U : W.Opens, IsAffineOpen U ∧ (U : Set W).Nonempty ∧
      ∀ O ∈ t, U ≤ O ∨ Disjoint (U : Set W) O := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    obtain ⟨x⟩ := ‹Nonempty W›
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, ⟨x, hx⟩, by simp⟩
  | insert O t _ ih =>
    obtain ⟨U, hU, hne, h⟩ := ih
    by_cases hd : Disjoint (U : Set W) O
    · refine ⟨U, hU, hne, fun O' hO' ↦ ?_⟩
      rcases Finset.mem_insert.mp hO' with rfl | hO'
      · exact .inr hd
      · exact h _ hO'
    · obtain ⟨x, hx⟩ := Set.not_disjoint_iff.mp hd
      obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ :=
        W.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U : Set W) ∩ O from hx)
          (U.isOpen.inter O.isOpen)
      refine ⟨U', hU', ⟨x, hx'⟩, fun O' hO' ↦ ?_⟩
      rcases Finset.mem_insert.mp hO' with rfl | hO'
      · exact .inl fun z hz ↦ (hle hz).2
      · rcases h _ hO' with h | h
        · exact .inl fun z hz ↦ h (hle hz).1
        · exact .inr (h.mono_left fun z hz ↦ (hle hz).1)

instance dominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage _⟩) ?_ fun U ↦ ?_
  · change ⨆ U : Y.affineOpens, f.imageι ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem surjective_algebraMap_zero (R : Type) [CommRing R] (N : ℕ) :
    Function.Surjective
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
  rintro ⟨p, hp⟩
  rw [MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
  exact ⟨p.coeff 0, Subtype.ext hp.symm⟩

theorem adjoin_X (R : Type) [CommRing R] (N : ℕ) :
    Algebra.adjoin ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R)) = ⊤ := by
  refine top_le_iff.mp fun p _ ↦ ?_
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) a)
  | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
  | mul_X p i hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

instance isProper_str (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    ⟨⟨(Set.finite_range MvPolynomial.X).toFinset, by
      rw [Set.Finite.coe_toFinset]; exact adjoin_X R N⟩⟩
  have : IsClosedImmersion
      (spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_algebraMap_zero R N)
  unfold PSpace.str
  infer_instance

def sec {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] (t : A) (z : HomogeneousLocalization.Away 𝒜 t) :
    Γ((Proj.basicOpen 𝒜 t).toScheme, ⊤) :=
  (Proj.basicOpenToSpec 𝒜 t).appTop ((Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 t))).inv z)

theorem basicOpen_sec {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1) :
    (Proj.basicOpen 𝒜 t).toScheme.basicOpen
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) =
      (Proj.basicOpen 𝒜 t).ι ⁻¹ᵁ Proj.basicOpen 𝒜 t' := by
  have h : (Proj.basicOpen 𝒜 t).ι =
      Proj.basicOpenToSpec 𝒜 t ≫ Proj.awayι 𝒜 t ht one_pos := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 t ht one_pos, Proj.awayι, Iso.hom_inv_id_assoc]
  rw [sec, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine, h, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 ht one_pos ht' one_pos]

set_option backward.isDefEq.respectTransparency false in
theorem sec_mul {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1)
    {U : Scheme.{0}} (F : A →+* Γ(U, ⊤)) :
    (Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht).appTop
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) *
      (U.basicOpen (F t)).ι.appTop (F t) = (U.basicOpen (F t)).ι.appTop (F t') := by
  let e : (U.basicOpen (F t)).toScheme ⟶ Spec (.of (Localization.Away (F t))) :=
    (U.isoOfEq (U.toSpecΓ_preimage_basicOpen (F t))).inv ≫ U.toSpecΓ ∣_ _ ≫
      (basicOpenIsoSpecAway (F t)).hom
  have he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (Localization.Away (F t)))) =
      (U.basicOpen (F t)).ι ≫ U.toSpecΓ := by
    simp only [e, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, morphismRestrict_ι,
      Scheme.isoOfEq_inv_ι_assoc]
  let ε : Localization.Away (F t) →+* Γ((U.basicOpen (F t)).toScheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Localization.Away (F t)))).inv ≫ e.appTop).hom
  have hε (y : Γ(U, ⊤)) : ε (algebraMap _ _ y) = (U.basicOpen (F t)).ι.appTop y := by
    have h1 := congrArg (fun φ ↦ ((Scheme.ΓSpecIso Γ(U, ⊤)).inv ≫ Scheme.Hom.appTop φ) y) he
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc] at h1
    exact h1
  let G : Localization.Away t →+* Localization.Away (F t) :=
    IsLocalization.map (M := .powers t) (T := .powers (F t)) _ F (by
      rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])
  have h2 : Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht ≫ Proj.basicOpenToSpec 𝒜 t =
      e ≫ Spec.map (CommRingCat.ofHom (G.comp (algebraMap (HomogeneousLocalization.Away 𝒜 t)
        (Localization.Away t)))) := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 t ht one_pos, Proj.toBasicOpenOfGlobalSections]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, e, G]
  have h3 (z : HomogeneousLocalization.Away 𝒜 t) :
      (Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht).appTop (sec 𝒜 t z) = ε (G z.val) := by
    have h1 := congrArg (fun φ ↦ ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop φ) z) h2
    simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] at h1
    exact h1
  rw [h3, ← hε, ← hε, ← map_mul]
  congr 1
  simp only [G, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    pow_one]
  exact IsLocalization.mk'_spec _ _ _

theorem exists_charts (R : Type) [CommRing R] (N : ℕ) :
    ∃ (D : Fin (N + 1) → (PSpace R N).Opens) (r : ∀ _ K, Γ((D K).toScheme, ⊤)),
      ⨆ K, D K = ⊤ ∧ (∀ J K, (D K).toScheme.basicOpen (r J K) ≤ (D K).ι ⁻¹ᵁ D J) ∧
      ∀ (U : Scheme.{0}) (u : U ⟶ Sp R) (m : Fin (N + 1) → Γ(U, ⊤)) (K₀ : Fin (N + 1)),
        IsUnit (m K₀) → ∃ φ : U ⟶ PSpace R N, φ ≫ PSpace.str R N = u ∧
          ∀ (K : Fin (N + 1)) (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D K), a ≫ φ = b ≫ (D K).ι →
            IsUnit (a.appTop (m K)) ∧
              ∀ J, b.appTop (r J K) * a.appTop (m K) = a.appTop (m J) := by
  have hX (K : Fin (N + 1)) : (MvPolynomial.X K : MvPolynomial (Fin (N + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 := MvPolynomial.isHomogeneous_X R K
  refine ⟨fun K ↦ Proj.basicOpen _ (MvPolynomial.X K),
    fun J K ↦ sec _ _ (HomogeneousLocalization.Away.isLocalizationElem (hX K) (hX J)),
    Proj.iSup_basicOpen_eq_top' _ _ (fun K ↦ ⟨1, hX K⟩) (adjoin_X R N),
    fun J K ↦ (basicOpen_sec _ (hX K) (hX J)).le, ?_⟩
  intro U u m K₀ hm
  let F : MvPolynomial (Fin (N + 1)) R →+* Γ(U, ⊤) :=
    MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ u.appTop).hom m
  have hF (K) : F (MvPolynomial.X K) = m K := MvPolynomial.eval₂Hom_X' _ _ _
  have hirr : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).toIdeal.map F = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ ?_ hm
    rw [← hF]
    refine Ideal.mem_map_of_mem _ ?_
    refine (HomogeneousIdeal.mem_irrelevant_iff _ _).mpr ?_
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ (hX K₀) one_ne_zero]
  refine ⟨Proj.fromOfGlobalSections _ F hirr, ?_, ?_⟩
  · rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have : (F.comp (algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) _)).comp
        (algebraMap R _) = ((Scheme.ΓSpecIso (.of R)).inv ≫ u.appTop).hom := by
      ext x
      exact MvPolynomial.eval₂Hom_C _ _ x
    rw [this, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  · intro K V a b hab
    have hpre := Proj.fromOfGlobalSections_preimage_basicOpen _ F hirr one_pos (hX K)
    have hr : Set.range a ⊆ Set.range (U.basicOpen (F (MvPolynomial.X K))).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, ← hpre]
      change Proj.fromOfGlobalSections _ F hirr (a z) ∈ Proj.basicOpen _ (MvPolynomial.X K)
      rw [← Scheme.Hom.comp_apply, hab, Scheme.Hom.comp_apply]
      exact (b z).2
    obtain ⟨a', rfl⟩ : ∃ a' : V ⟶ (U.basicOpen (F (MvPolynomial.X K))).toScheme,
        a' ≫ (U.basicOpen (F (MvPolynomial.X K))).ι = a :=
      ⟨_, IsOpenImmersion.lift_fac _ a hr⟩
    obtain rfl : b = a' ≫ Proj.toBasicOpenOfGlobalSections _ F rfl one_pos (hX K) := by
      rw [← cancel_mono (Scheme.Opens.ι _), ← hab,
        ← Proj.fromOfGlobalSections_resLE _ F hirr one_pos (hX K), Category.assoc, Category.assoc,
        Scheme.Hom.resLE_comp_ι]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← hF]
    refine ⟨IsUnit.map _ ?_, fun J ↦ ?_⟩
    · apply RingedSpace.isUnit_of_isUnit_germ
      intro x hx
      rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen_top]
      exact x.2
    · rw [← map_mul, sec_mul _ (hX K) (hX J)]

theorem closed_on_chart {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated f]
    (U O : W.Opens) (hUO : U ≤ O) (φ : U.toScheme ⟶ P) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) (h₂ : j ≫ ι ≫ pullback.snd f s = φ)
    {σ : Type} (g : σ → Γ(O.toScheme, ⊤))
    [IsClosedImmersion (AffineSpace.homOfVector (O.ι ≫ f) g)]
    (D : P.Opens) (r : σ → Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      ∀ i, b.appTop (r i) = a.appTop ((W.homOfLE hUO).appTop (g i))) :
    IsClosedImmersion ((ι ≫ pullback.snd f s) ∣_ D) := by
  let c := AffineSpace.homOfVector (O.ι ≫ f) g
  let h := AffineSpace.homOfVector (D.ι ≫ s) r
  have hc : c ≫ 𝔸(σ; S) ↘ S = O.ι ≫ f := AffineSpace.homOfVector_over _ _
  have hh : h ≫ 𝔸(σ; S) ↘ S = D.ι ≫ s := AffineSpace.homOfVector_over _ _
  have hφ : φ ≫ s = U.ι ≫ f := by
    rw [← h₁, ← h₂]; simp [pullback.condition]
  refine closed_restrict_of_dense (pullback.snd f s) ι j D (pullback.snd c h)
    (pullback.lift (pullback.fst c h ≫ O.ι) (pullback.snd c h ≫ D.ι) (by
      rw [Category.assoc, Category.assoc, ← hc, ← hh, pullback.condition_assoc]))
    (pullback.lift_snd _ _ _) ?_
  intro Z a b hab
  rw [h₂] at hab
  refine ⟨pullback.lift (a ≫ W.homOfLE hUO) b ?_, ?_⟩
  · apply AffineSpace.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, hc, hh, Scheme.homOfLE_ι_assoc,
        ← reassoc_of% hab, hφ]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, c, h,
        AffineSpace.homOfVector_appTop_coord]
      exact (hr Z a b hab i).symm
  · apply pullback.hom_ext
    · simp [h₁, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [h₂, hab, pullback.lift_snd, pullback.lift_snd_assoc]

theorem isIso_on_open {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated s]
    (U : W.Opens) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) :
    IsIso ((ι ≫ pullback.fst f s) ∣_ U) := by
  have : IsClosedImmersion ((ι ≫ pullback.fst f s) ∣_ U) :=
    closed_restrict_of_dense (pullback.fst f s) ι j U (𝟙 _) (j ≫ ι) (by simp [h₁])
      fun Z a _ _ ↦ ⟨a, rfl⟩
  have hr : Set.range j ⊆ Set.range ((ι ≫ pullback.fst f s) ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (ι ≫ pullback.fst f s) (j z) ∈ U
    rw [← Scheme.Hom.comp_apply, h₁]
    exact z.2
  have : IsSplitEpi ((ι ≫ pullback.fst f s) ∣_ U) :=
    ⟨⟨IsOpenImmersion.lift _ j hr, by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
        IsOpenImmersion.lift_fac_assoc, h₁, Category.id_comp]⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

theorem mem_basicOpen_of_mul_eq_one {W P X : Scheme.{0}} (U O : W.Opens) (hUO : U ≤ O)
    (φ : U.toScheme ⟶ P) (π : X ⟶ W) (q : X ⟶ P)
    (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ π = U.ι) (h₂ : j ≫ q = φ) (g : Γ(O.toScheme, ⊤))
    (D : P.Opens) (r : Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      b.appTop r * a.appTop ((W.homOfLE hUO).appTop g) = 1)
    (x : X) (hO : π x ∈ O) (hD : q x ∈ D) :
    ∃ z : D.toScheme, z ∈ D.toScheme.basicOpen r ∧ D.ι z = q x := by
  let V : X.Opens := π ⁻¹ᵁ O ⊓ q ⁻¹ᵁ D
  let α : V.toScheme ⟶ O := π.resLE O V inf_le_left
  let β : V.toScheme ⟶ D := q.resLE D V inf_le_right
  have hα : α ≫ O.ι = V.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hβ : β ≫ D.ι = V.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  have e₁ : j ∣_ V ≫ α = (j ⁻¹ᵁ V).ι ≫ W.homOfLE hUO := by
    rw [← cancel_mono O.ι, Category.assoc, hα, morphismRestrict_ι_assoc, h₁, Category.assoc,
      Scheme.homOfLE_ι]
  have e₂ := hr _ (j ⁻¹ᵁ V).ι (j ∣_ V ≫ β) (by
    rw [Category.assoc, hβ, morphismRestrict_ι_assoc, h₂])
  have e₃ : β.appTop r * α.appTop g = 1 := by
    apply (j ∣_ V).app_injective ⊤
    change (j ∣_ V).appTop _ = (j ∣_ V).appTop _
    rw [map_mul, map_one, ← e₂, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e₁, Scheme.Hom.comp_appTop (j ⁻¹ᵁ V).ι,
      CommRingCat.comp_apply]
  have e₄ : β ⁻¹ᵁ D.toScheme.basicOpen r = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact Scheme.basicOpen_of_isUnit _ (IsUnit.of_mul_eq_one _ e₃)
  refine ⟨β ⟨x, hO, hD⟩, e₄.ge (Set.mem_univ (⟨x, hO, hD⟩ : V.toScheme)), ?_⟩
  exact (Scheme.Hom.comp_apply β D.ι _).symm.trans congr($hβ ⟨x, hO, hD⟩)

theorem chow (R : Type) [CommRing R] [IsNoetherianRing R] (W : Scheme)
    (f : W ⟶ Spec (CommRingCat.of R)) (hsep : IsSeparated f) (hft : LocallyOfFiniteType f)
    (hqc : QuasiCompact f) (hne : Nonempty W) :
    ∃ (W' : Scheme) (P : Scheme) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R))
      (U : W.Opens), IsProper π ∧ Set.Nonempty (U : Set W) ∧ IsIso (π ∣_ U) ∧ IsProjOver s ∧
        IsImmersion q ∧ q ≫ s = π ≫ f := by
  classical
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨t, ht, hcov⟩ : ∃ t : Finset W.Opens, (∀ O ∈ t, IsAffineOpen O) ∧
      ∀ x : W, ∃ O ∈ t, x ∈ O := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun O : W.affineOpens ↦ (O.1 : Set W))
      (fun O ↦ O.1.isOpen) (fun x _ ↦ by
        obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
          W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩)
    refine ⟨t.image Subtype.val, ?_, fun x ↦ ?_⟩
    · intro O hO
      obtain ⟨O, -, rfl⟩ := Finset.mem_image.mp hO
      exact O.2
    · obtain ⟨O, hO, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact ⟨O.1, Finset.mem_image_of_mem _ hO, hx⟩
  obtain ⟨U, hU, hUne, hdich⟩ := exists_affine_le_or_disjoint t
  let I : Type := {O : t // U ≤ O.1}
  have hgen (i : I) : ∃ (σ : Type) (_ : Fintype σ) (g : σ → Γ(i.1.1.toScheme, ⊤)),
      IsClosedImmersion (AffineSpace.homOfVector (i.1.1.ι ≫ f) g) := by
    have : IsAffine i.1.1.toScheme := ht _ i.1.2
    exact exists_closed_affineSpace _
  choose σ hσ g hg using hgen
  let x (i : I) (a : Option (σ i)) : Γ(U.toScheme, ⊤) :=
    (W.homOfLE i.2).appTop (a.elim 1 (g i))
  let m (K : ∀ i, Option (σ i)) : Γ(U.toScheme, ⊤) := ∏ i, x i (K i)
  have hx0 (i : I) : x i none = 1 := map_one _
  have hm0 : m (fun _ ↦ none) = 1 := Finset.prod_eq_one fun i _ ↦ hx0 i
  have hm (K : ∀ i, Option (σ i)) (i : I) (hK : K i = none) (a : Option (σ i)) :
      m (Function.update K i a) = x i a * m K := by
    simp only [m]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self,
      ← Finset.mul_prod_erase _ (fun i ↦ x i (K i)) (Finset.mem_univ i), hK, hx0, one_mul]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (∀ i, Option (σ i)) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e := Fintype.equivFinOfCardEq hN
  obtain ⟨D, r, hD, hr, hφ⟩ := exists_charts R N
  obtain ⟨φ, hφs, hφ⟩ := hφ U (U.ι ≫ f) (fun K ↦ m (e.symm K)) (e fun _ ↦ none)
    (by rw [e.symm_apply_apply, hm0]; exact isUnit_one)
  let s := PSpace.str R N
  let γ : U.toScheme ⟶ pullback f s := pullback.lift U.ι φ hφs.symm
  have : IsAffine U.toScheme := hU
  have : QuasiCompact (γ ≫ pullback.fst f s ≫ f) := inferInstance
  have : QuasiCompact γ := QuasiCompact.of_comp γ (pullback.fst f s ≫ f)
  have h₁ : γ.toImage ≫ γ.imageι ≫ pullback.fst f s = U.ι := by
    rw [γ.toImage_imageι_assoc, pullback.lift_fst]
  have h₂ : γ.toImage ≫ γ.imageι ≫ pullback.snd f s = φ := by
    rw [γ.toImage_imageι_assoc, pullback.lift_snd]
  refine ⟨γ.image, PSpace R N, γ.imageι ≫ pullback.fst f s, γ.imageι ≫ pullback.snd f s, s, U,
    inferInstance, hUne, isIso_on_open f s U _ γ.toImage h₁,
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_, by simp [pullback.condition]⟩
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun _ _ _ _ ↦ inferInstance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion)
    (fun K : {K : ∀ i, Option (σ i) // ∃ i, K i = none} ↦ D (e K.1)) ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨O, hOt, hzO⟩ := hcov ((γ.imageι ≫ pullback.fst f s) z)
    have hUO : U ≤ O := by
      refine (hdich O hOt).resolve_right fun hdis ↦ ?_
      obtain ⟨w, hw⟩ := γ.toImage.denseRange.exists_mem_open
        ((γ.imageι ≫ pullback.fst f s) ⁻¹ᵁ O).isOpen ⟨z, hzO⟩
      change (γ.imageι ≫ pullback.fst f s) (γ.toImage w) ∈ O at hw
      rw [← Scheme.Hom.comp_apply, h₁] at hw
      exact Set.disjoint_left.mp hdis w.2 hw
    let i : I := ⟨⟨O, hOt⟩, hUO⟩
    obtain ⟨K, hK⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hD.ge (Set.mem_univ ((γ.imageι ≫ pullback.snd f s) z)))
    obtain ⟨K, rfl⟩ := e.surjective K
    obtain ⟨w, hw, hwz⟩ := mem_basicOpen_of_mul_eq_one U O hUO φ _ _ γ.toImage h₁ h₂
      ((K i).elim 1 (g i)) (D (e K)) (r (e (Function.update K i none)) (e K)) (by
        intro V a b hab
        obtain ⟨hu, hb⟩ := hφ (e K) V a b hab
        have hb' := hb (e (Function.update K i none))
        simp only [e.symm_apply_apply] at hu hb'
        have hK' := hm (Function.update K i none) i (Function.update_self _ _ _) (K i)
        rw [Function.update_idem, Function.update_eq_self] at hK'
        refine hu.mul_left_inj.mp ?_
        rw [mul_right_comm, hb', one_mul, ← map_mul, mul_comm, hK']) z hzO hK
    refine TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨Function.update K i none, i, Function.update_self _ _ _⟩, ?_⟩
    rw [← hwz]
    exact hr _ _ hw
  · rintro ⟨K, i, hK⟩
    have := hg i
    have := closed_on_chart f s U i.1.1 i.2 φ γ.imageι γ.toImage h₁ h₂ (g i) (D (e K))
      (fun a ↦ r (e (Function.update K i (some a))) (e K)) (by
        intro V a b hab c
        obtain ⟨hu, hb⟩ := hφ (e K) V a b hab
        have hb' := hb (e (Function.update K i (some c)))
        simp only [e.symm_apply_apply] at hu hb'
        refine hu.mul_left_inj.mp ?_
        rw [hb', hm K i hK, map_mul]
        rfl)
    exact inferInstanceAs (IsImmersion ((γ.imageι ≫ pullback.snd f s) ∣_ D (e K)))

end GlobalTheory.DenseClosedAffineSubsets
