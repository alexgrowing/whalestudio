import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SaturationByPowers
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable def saturationByPowers {A : Type*} [CommRing A] (J : Ideal A) (a : A) : Ideal A :=
  _root_.UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers J a

theorem mem_saturationByPowers_iff {A : Type*} [CommRing A] (J : Ideal A) (a x : A) :
    x ∈ saturationByPowers J a ↔ ∃ n : ℕ, a ^ n * x ∈ J := Iff.rfl

private theorem map_saturationByPowers_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) ≤
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  rw [Ideal.map_le_iff_le_comap]
  rintro x ⟨n, hn⟩
  rw [Ideal.mem_comap, mem_saturationByPowers_iff]
  refine ⟨n, ?_⟩
  have h := Ideal.mem_map_of_mem (algebraMap A B) hn
  rwa [map_mul, map_pow] at h

theorem map_saturationByPowers_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) =
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  refine le_antisymm (map_saturationByPowers_le J a) ?_
  rintro y ⟨n, hy⟩
  obtain ⟨u, hu⟩ : ∃ u : A →ₗ[A] (A ⧸ J), u = J.mkQ ∘ₗ LinearMap.lsmul A A (a ^ n) := ⟨_, rfl⟩
  have hker : ∀ c : A, u c = 0 ↔ a ^ n * c ∈ J := by
    intro c
    rw [hu, LinearMap.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
  have hex : Function.Exact (LinearMap.ker u).subtype u := by
    intro c
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact hc
  have hflat : Function.Exact (LinearMap.lTensor B (LinearMap.ker u).subtype)
      (LinearMap.lTensor B u) := Module.Flat.lTensor_exact B hex
  have key : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = 0 := by
    have hmapJ : (Ideal.map (algebraMap A B) J : Ideal B)
        = Ideal.span (⇑(algebraMap A B) '' (J : Set A)) := rfl
    rw [hmapJ] at hy
    obtain ⟨k, cf, gg, hsum⟩ := Submodule.mem_span_set'.1 hy
    have hgg : ∀ i, ∃ c : A, c ∈ J ∧ algebraMap A B c = (gg i : B) := by
      intro i
      obtain ⟨c, hc1, hc2⟩ := (gg i).2
      exact ⟨c, hc1, hc2⟩
    choose c hcJ hcmap using hgg
    have e1 : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = y ⊗ₜ[A] (J.mkQ (a ^ n)) := by
      rw [LinearMap.lTensor_tmul, hu]
      simp
    have e2 : (J.mkQ (a ^ n) : A ⧸ J) = (a ^ n) • (J.mkQ (1 : A)) := by
      rw [← map_smul]
      simp
    have e3 : algebraMap A B (a ^ n) * y = ∑ i, c i • cf i := by
      rw [map_pow, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcmap i, smul_eq_mul, Algebra.smul_def]
      ring
    rw [e1, e2, ← TensorProduct.smul_tmul, Algebra.smul_def, e3, TensorProduct.sum_tmul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [TensorProduct.smul_tmul]
    have hz : (c i) • (J.mkQ (1 : A)) = 0 := by
      have hz1 : (c i) • (J.mkQ (1 : A)) = J.mkQ (c i) := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [hz1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hcJ i
    rw [hz, TensorProduct.tmul_zero]
  obtain ⟨w, hw⟩ := (hflat (y ⊗ₜ[A] (1 : A))).1 key
  have main : ∀ z : TensorProduct A B (LinearMap.ker u),
      TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype z) ∈
        (saturationByPowers J a).map (algebraMap A B) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b cc =>
        have hcc : (cc : A) ∈ saturationByPowers J a := ⟨n, (hker _).1 cc.2⟩
        have h2 : algebraMap A B (cc : A) * b ∈ (saturationByPowers J a).map (algebraMap A B) :=
          Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem (algebraMap A B) hcc)
        simpa [Algebra.smul_def] using h2
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Ideal.add_mem _ h₁ h₂
  have hy2 : y = TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype w) := by
    rw [hw]
    simp
  rw [hy2]
  exact main w

private theorem exists_pow_mul_mem_of_mem_map_away {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (f : A) [IsLocalization.Away f B] (I : Ideal A) (x : A)
    (hx : algebraMap A B x ∈ I.map (algebraMap A B)) : ∃ n : ℕ, f ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) B] at hx
  obtain ⟨⟨i, m⟩, hxe⟩ := hx
  obtain ⟨p, hp⟩ := m.2
  have hp' : f ^ p = (m : A) := hp
  have h2 : algebraMap A B (x * (m : A)) = algebraMap A B (i : A) := by
    rw [map_mul]
    exact hxe
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) B).1 h2
  obtain ⟨q, hq⟩ := cc.2
  have hq' : f ^ q = (cc : A) := hq
  refine ⟨q + p, ?_⟩
  have h3 : f ^ (q + p) * x = (cc : A) * (x * (m : A)) := by
    rw [pow_add, hp', hq']; ring
  rw [h3, hcc]
  exact I.mul_mem_left _ i.2

private theorem exists_pow_mul_mem_of_mem_map_basicOpen {X : Scheme.{u}} (U : X.affineOpens)
    (f : Γ(X, U.1)) (I : Ideal Γ(X, U.1)) (x : Γ(X, U.1))
    (hx : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) I) :
    ∃ n : ℕ, f ^ n * x ∈ I := by
  have := U.2.isLocalization_basicOpen f
  exact exists_pow_mul_mem_of_mem_map_away (A := Γ(X, U.1)) (B := Γ(X, X.basicOpen f)) f I x hx

private theorem span_eq_top_of_basicOpen_cover {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ y : X, y ∈ U → ∃ f ∈ s, y ∈ X.basicOpen f) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
  have hmp : m.IsPrime := hm.isPrime
  have hy : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈ U := by
    have hr : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈
        Set.range (IsAffineOpen.fromSpec hU).base := Set.mem_range_self _
    rwa [IsAffineOpen.range_fromSpec] at hr
  obtain ⟨f, hfs, hf⟩ := hcov _ hy
  have h1 : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈
      (IsAffineOpen.fromSpec hU) ⁻¹ᵁ X.basicOpen f := hf
  rw [IsAffineOpen.fromSpec_preimage_basicOpen hU f] at h1
  exact ((PrimeSpectrum.mem_basicOpen f _).1 h1) (hsm (Ideal.subset_span hfs))

private theorem ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top {X : Scheme.{u}} (I J : X.IdealSheafData)
    (U : X.affineOpens) (s : Set Γ(X, U.1)) (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal U = J.ideal U := by
  have key : ∀ P Q : X.IdealSheafData,
      (∀ f ∈ s, P.ideal (X.affineBasicOpen f) = Q.ideal (X.affineBasicOpen f)) →
      P.ideal U ≤ Q.ideal U := by
    intro P Q hPQ x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x ?_
    rintro ⟨f, hf⟩
    have h1 : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
        Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op))
          (Q.ideal U) := by
      rw [Q.2 U f, ← hPQ f hf, ← P.2 U f]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_mem_map_basicOpen U f (Q.ideal U) x h1
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  exact le_antisymm (key I J h) (key J I fun f hf => (h f hf).symm)

private theorem ideal_comap_saturation_of_ideal_eq_span_singleton {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [AlgebraicGeometry.Flat g] (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))]
    (U : Y.affineOpens) (V : Y'.affineOpens)
    (e : (V : Y'.Opens) ≤ (TopologicalSpace.Opens.map g.base).obj (U : Y.Opens))
    (t : Γ(Y, U.1)) (ht : F.ideal U = Ideal.span {t}) :
    ((saturation F T).comap g).ideal V = (saturation (F.comap g) (T.comap g)).ideal V := by
  let _ : Algebra Γ(Y, U.1) Γ(Y', V.1) := (CommRingCat.Hom.hom (g.appLE U.1 V.1 e)).toAlgebra
  have halg : algebraMap Γ(Y, U.1) Γ(Y', V.1) = CommRingCat.Hom.hom (g.appLE U.1 V.1 e) := rfl
  have : Module.Flat Γ(Y, U.1) Γ(Y', V.1) :=
    (inferInstance : AlgebraicGeometry.Flat g).1 U.2 V.2 e
  have h1 : ((saturation F T).comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) ((saturation F T).ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h3 : (T.comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) (T.ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h2 : (saturation F T).ideal U = saturationByPowers (T.ideal U) t := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff F T U t ht w
  have h4 : (F.comap g).ideal V = Ideal.span {algebraMap Γ(Y, U.1) Γ(Y', V.1) t} := by
    rw [halg]
    have hh := Scheme.IdealSheafData.comap_ideal_eq_span_image F g U V e {t} ht
    simpa using hh
  have h5 : (saturation (F.comap g) (T.comap g)).ideal V
      = saturationByPowers ((T.comap g).ideal V) (algebraMap Γ(Y, U.1) Γ(Y', V.1) t) := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff (F.comap g) (T.comap g) V _ h4 w
  rw [h1, h2, h5, h3]
  exact map_saturationByPowers_of_flat (T.ideal U) t

theorem comap_saturation_of_flat {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [AlgebraicGeometry.Flat g] (F T : Y.IdealSheafData) (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))] :
    (saturation F T).comap g = saturation (F.comap g) (T.comap g) := by
  classical
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  refine ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top _ _ V
    {f : Γ(Y', V.1) | ∃ (U : Y.affineOpens) (t : Γ(Y, U.1)), F.ideal U = Ideal.span {t} ∧
      Y'.basicOpen f ≤ (TopologicalSpace.Opens.map g.base).obj U.1} ?_ ?_
  · refine span_eq_top_of_basicOpen_cover V.1 V.2 _ ?_
    intro y hy
    obtain ⟨U, t, hUmem, -, ht⟩ := hF (g.base y)
    obtain ⟨f, hf1, hf2⟩ := IsAffineOpen.exists_basicOpen_le V.2
      (⟨y, ⟨hy, hUmem⟩⟩ : (V.1 ⊓ (TopologicalSpace.Opens.map g.base).obj U.1 : Y'.Opens)) hy
    exact ⟨f, ⟨U, t, ht, le_trans hf1 inf_le_right⟩, hf2⟩
  · rintro f ⟨U, t, ht, hle⟩
    exact ideal_comap_saturation_of_ideal_eq_span_singleton g F T U (Y'.affineBasicOpen f) hle t ht

theorem comap_strictTransform_of_flat {X X₁ X' X₁' : Scheme.{u}}
    (π : X₁ ⟶ X) (g : X' ⟶ X) (π' : X₁' ⟶ X') (g₁ : X₁' ⟶ X₁)
    [AlgebraicGeometry.Flat g]
    (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g))] :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have hZ : (Z.comap π).comap g₁ = (Z.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have hD : (D.comap π).comap g₁ = (D.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have : AlgebraicGeometry.Flat g₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Flat)
      hsq.flip inferInstance
  have i1 : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have i2 : QuasiCompact (saturationι ((Z.comap π).comap g₁) ((D.comap π).comap g₁)) := by
    rw [hZ, hD]
    exact inferInstanceAs (QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g)))
  have h := comap_saturation_of_flat g₁ (Z.comap π) (D.comap π) hπ.1
  simp only [strictTransform_eq_saturation]
  rw [h, hZ, hD]

theorem comap_strictTransform_of_flat_of_isLocallyNoetherian {X X₁ X' X₁' : Scheme.{u}}
    (π : X₁ ⟶ X) (g : X' ⟶ X) (π' : X₁' ⟶ X') (g₁ : X₁' ⟶ X₁)
    [AlgebraicGeometry.Flat g] [IsLocallyNoetherian X₁] [IsLocallyNoetherian X₁']
    (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π' (Z.comap g) (D.comap g)
  exact comap_strictTransform_of_flat π g π' g₁ hsq Z D hπ

end FunctorialResolution.EmbeddedResolution
