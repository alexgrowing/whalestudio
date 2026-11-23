import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SliceHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.DehHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem localized_length_le_one {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime]
    (hk : ∀ p ∈ P, ∀ m : M, ∃ b, b ∉ P ∧ (b * p) • m = 0)
    (m0 : M) (hc : ∀ m : M, ∃ b, b ∉ P ∧ ∃ a : B, b • m = a • m0) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) ≤ 1 := by
  let R := Localization.AtPrime P
  let φ : R →ₗ[R] LocalizedModule P.primeCompl M :=
    LinearMap.toSpanSingleton R _ (LocalizedModule.mk m0 1)
  have hs : Function.Surjective φ := by
    intro y
    induction y using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨b, hb, a, hab⟩ := hc m
      refine ⟨Localization.mk a (⟨b, hb⟩ * s), ?_⟩
      show Localization.mk a ((⟨b, hb⟩ : P.primeCompl) * s) • LocalizedModule.mk m0 (1 : P.primeCompl) = _
      rw [LocalizedModule.mk_smul_mk, mul_one, ← hab]
      exact LocalizedModule.mk_cancel_common_left (⟨b, hb⟩ : P.primeCompl) s m
  have hker : maximalIdeal R ≤ LinearMap.ker φ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro p hp
    obtain ⟨b, hb, h⟩ := hk p hp m0
    show algebraMap B R p • LocalizedModule.mk m0 (1 : P.primeCompl) = 0
    rw [algebraMap_smul, LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : P.primeCompl),
      LocalizedModule.mk_eq]
    refine ⟨⟨b, hb⟩, ?_⟩
    simpa [Submonoid.smul_def, mul_smul] using h
  have hs' : Function.Surjective ((maximalIdeal R).liftQ φ hker) := by
    intro y
    obtain ⟨r, rfl⟩ := hs y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hsimple : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 inferInstance)
  calc _ ≤ Module.length R (R ⧸ maximalIdeal R) := Module.length_le_of_surjective _ hs'
    _ = 1 := Module.length_eq_one R _

private theorem nilpotent_modulo_kernel {O K A : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [FaithfulSMul O K]
    [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (I : Ideal A) (h2 : M2 𝒜 I)
    (σ : 𝒜 0 →ₐ[O] K) (p : 𝒜 0) (hp : σ p = 0) :
    ∃ b : 𝒜 0, σ b ≠ 0 ∧ ∃ n : ℕ, (b : A) * (p : A) ^ n ∈ I := by
  let ψ : 𝒜 0 →ₐ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).comp (IsScalarTower.toAlgHom O (𝒜 0) A)
  have hfg : (Subalgebra.toSubmodule ψ.range).FG := by
    have : Subalgebra.toSubmodule ψ.range = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, b.2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    rw [this]; exact h2
  obtain ⟨q, hq, hq0⟩ := IsIntegral.of_mem_of_fg ψ.range hfg (ψ p) ⟨p, rfl⟩
  obtain ⟨r, hr, hr0⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq.ne_zero 0
  rw [Polynomial.dvd_iff_isRoot] at hr0
  refine ⟨Polynomial.aeval p r, ?_, q.rootMultiplicity 0, ?_⟩
  · rw [← Polynomial.aeval_algHom_apply, hp, ← map_zero (algebraMap O K), Polynomial.aeval_algebraMap_apply]
    intro h
    exact hr0 (FaithfulSMul.algebraMap_injective O K h)
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : ψ (Polynomial.aeval p q) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact hq0
    rw [hr] at h1
    simp only [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_zero, sub_zero] at h1
    rw [map_mul, map_pow, mul_comm]
    exact h1

theorem UpperTheory.V.Alg.M.locLen_quotientWeightPiece_le_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∀ σ : 𝒜 0 →ₐ[O] K, ¬ idD 𝒜 ≤ RingHom.ker σ →
      ∀ w, locLen σ (aPiece 𝒜 I w) ≤ 1 := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4 σ hσ w
  obtain ⟨τ, ⟨f, hf, g, hg, hτ⟩, hστ⟩ : ∃ τ : 𝒜 0, (∃ f ∈ 𝒜 (-2), ∃ g ∈ 𝒜 2, (τ : A) = f * g) ∧ σ τ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hσ (Ideal.span_le.2 fun b hb => hcon b hb)
  have red : ∀ (j : ℤ) (h : A), h ∈ 𝒜 j → ∀ b : 𝒜 0, σ b ≠ 0 → ∀ n : ℕ, (b : A) * h ^ n ∈ I →
      ∃ b' : 𝒜 0, σ b' ≠ 0 ∧ (b' : A) * h ∈ I := by
    intro j h hh b hb n hn
    obtain ⟨N, c, hc, hmem⟩ := (slice_holds O K A 𝒜 x hx I hI h2 h4 f hf g hg).2 ((b : A) * h) (by
      intro ξ hξ _ _
      have := hξ _ hn
      rw [map_mul, map_pow, mul_eq_zero] at this
      rw [map_mul, mul_eq_zero]
      exact this.imp id fun h' => eq_zero_of_pow_eq_zero h')
    have hhom : c • (g ^ N * ((b : A) * h)) ∈ 𝒜 (N • (2 : ℤ) + (0 + j)) :=
      Submodule.smul_mem _ c (SetLike.mul_mem_graded (SetLike.pow_mem_graded N hg) (SetLike.mul_mem_graded b.2 hh))
    obtain ⟨m, hm⟩ := deh_holds O A 𝒜 I hI (-2) _ f _ (by norm_num) hf hhom hmem
    refine ⟨c • (τ ^ (N + m) * b), ?_, ?_⟩
    · rw [map_smul, map_mul, map_pow, Algebra.smul_def]
      exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 hc)
        (mul_ne_zero (pow_ne_zero _ hστ) hb)
    · have : ((c • (τ ^ (N + m) * b) : 𝒜 0) : A) * h = (f ^ N * g ^ m) * (f ^ m * c • (g ^ N * ((b : A) * h))) := by
        rw [Submodule.coe_smul, SetLike.GradeZero.coe_mul, SetLike.GradeZero.coe_pow, hτ, Algebra.smul_def,
          Algebra.smul_def]
        ring
      rw [this]
      exact I.mul_mem_left _ hm
  obtain ⟨e, he, e', k, hee⟩ : ∃ e ∈ 𝒜 (-2 * w), ∃ e' : A, ∃ k : ℕ, e * e' = (τ : A) ^ k := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
    · refine ⟨f ^ k, ?_, g ^ k, k, by rw [hτ, mul_pow]⟩
      have := SetLike.pow_mem_graded k hf
      rwa [nsmul_eq_mul, mul_comm] at this
    · refine ⟨g ^ k, ?_, f ^ k, k, by rw [hτ, mul_pow, mul_comm]⟩
      have := SetLike.pow_mem_graded k hg
      rwa [nsmul_eq_mul, show (k : ℤ) * 2 = -2 * -(k : ℤ) by ring] at this
  have hprod : ∀ h ∈ 𝒜 w, ∀ h' ∈ 𝒜 w, h * h' * e ∈ 𝒜 0 := fun h hh h' hh' => by
    have := SetLike.mul_mem_graded (SetLike.mul_mem_graded hh hh') he
    rwa [show w + w + -2 * w = 0 by ring] at this
  have cyc : ∃ h0 ∈ 𝒜 w, ∀ h ∈ 𝒜 w, ∃ b : 𝒜 0, σ b ≠ 0 ∧ ∃ a : 𝒜 0, (b : A) * h - (a : A) * h0 ∈ I := by
    by_cases hall : ∀ h (hh : h ∈ 𝒜 w), σ ⟨h * h * e, hprod h hh h hh⟩ = 0
    · refine ⟨0, zero_mem _, fun h hh => ?_⟩
      obtain ⟨b, hb, n, hn⟩ := nilpotent_modulo_kernel 𝒜 I h2 σ _ (hall h hh)
      obtain ⟨b', hb', h'⟩ := red w h hh (b * (τ ^ k) ^ n) (by
        rw [map_mul, map_pow, map_pow]
        exact mul_ne_zero hb (pow_ne_zero _ (pow_ne_zero _ hστ))) (2 * n) (by
        have : ((b * (τ ^ k) ^ n : 𝒜 0) : A) * h ^ (2 * n) = e' ^ n * ((b : A) * (h * h * e) ^ n) := by
          rw [SetLike.GradeZero.coe_mul, SetLike.GradeZero.coe_pow, SetLike.GradeZero.coe_pow, ← hee]
          ring
        rw [this]
        exact I.mul_mem_left _ hn)
      exact ⟨b', hb', 0, by simpa using h'⟩
    · push Not at hall
      obtain ⟨h0, hh0, hne⟩ := hall
      refine ⟨h0, hh0, fun h hh => ⟨_, hne, ⟨h * h0 * e, hprod h hh h0 hh0⟩, ?_⟩⟩
      have : h0 * h0 * e * h - h * h0 * e * h0 = 0 := by ring
      show h0 * h0 * e * h - h * h0 * e * h0 ∈ I
      rw [this]; exact I.zero_mem
  obtain ⟨h0, hh0, hcyc⟩ := cyc
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  refine localized_length_le_one (RingHom.ker σ) ?_ (⟨Ideal.Quotient.mk I h0, h0, hh0, rfl⟩ : aPiece 𝒜 I w) ?_
  · rintro p hp ⟨_, h, hh, rfl⟩
    obtain ⟨b, hb, n, hn⟩ := nilpotent_modulo_kernel 𝒜 I h2 σ p hp
    obtain ⟨b', hb', h'⟩ := red (0 + w) ((p : A) * h) (SetLike.mul_mem_graded p.2 hh) b hb n (by
      rw [mul_pow, ← mul_assoc]; exact I.mul_mem_right _ hn)
    refine ⟨b', hb', Subtype.ext ?_⟩
    show Ideal.Quotient.mk I (((b' : A) * p) * h) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc]
    exact h'
  · rintro ⟨_, h, hh, rfl⟩
    obtain ⟨b, hb, a, hab⟩ := hcyc h hh
    refine ⟨b, hb, a, Subtype.ext ?_⟩
    show Ideal.Quotient.mk I ((b : A) * h) = Ideal.Quotient.mk I ((a : A) * h0)
    exact Ideal.Quotient.eq.2 hab
