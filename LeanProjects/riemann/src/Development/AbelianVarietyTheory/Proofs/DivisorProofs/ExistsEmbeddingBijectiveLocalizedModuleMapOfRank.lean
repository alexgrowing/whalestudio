import Mathlib

namespace GlobalTheory

open Module

theorem localizedModule_map_injective_of_surjective_of_rankAtStalk
    {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
    (r : ℕ) (P : PrimeSpectrum R) (hP : Module.rankAtStalk Q P = r) (φ : (Fin r → R) →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl φ)) :
    Function.Injective (LocalizedModule.map P.asIdeal.primeCompl φ) := by
  haveI : Nontrivial R := nontrivial_of_ne (0 : R) 1 fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ P.asIdeal.zero_mem))
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) = r := by
    have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := Fin r → R)) P
    rw [Module.finrank_fin_fun] at this
    exact this
  have h2 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) = r := hP
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap _ e.injective hs

theorem exists_smul_mem_range_of_surjective_localizedModule_map
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] (P : Ideal R) [P.IsPrime] (φ : M →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.primeCompl φ)) :
    ∃ f ∉ P, ∀ q : Q, f • q ∈ LinearMap.range φ := by
  have key : ∀ g : Q, ∃ a ∈ P.primeCompl, a • g ∈ LinearMap.range φ := by
    intro g
    obtain ⟨y, hy⟩ := hs (LocalizedModule.mk g 1)
    induction y using LocalizedModule.induction_on with
    | h x t =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨(u : R) * t, P.primeCompl.mul_mem u.2 t.2, ⟨(u : R) • x, ?_⟩⟩
      rw [map_smul, mul_smul]
      simpa [Submonoid.smul_def] using hu
  classical
  choose a ha hga using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Q)
  refine ⟨∏ g ∈ s, a g, fun h => ?_, ?_⟩
  · exact (Submonoid.prod_mem P.primeCompl fun g _ => ha g) h
  · have hle : Submodule.span R (s : Set Q) ≤
        (LinearMap.range φ).comap (LinearMap.lsmul R Q (∏ g ∈ s, a g)) := by
      rw [Submodule.span_le]
      intro g hg
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
      rw [← Finset.prod_erase_mul s a hg, mul_smul]
      exact Submodule.smul_mem _ _ (hga g)
    intro q
    have := hle (hs ▸ Submodule.mem_top : q ∈ Submodule.span R (s : Set Q))
    simpa using this

theorem localizedModule_map_surjective_of_smul_mem_range
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (S : Submonoid R) (φ : M →ₗ[R] Q) (f : R) (hf : f ∈ S)
    (h : ∀ q : Q, f • q ∈ LinearMap.range φ) :
    Function.Surjective (LocalizedModule.map S φ) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | h q s =>
    obtain ⟨x, hx⟩ := h q
    refine ⟨LocalizedModule.mk x (⟨f, hf⟩ * s), ?_⟩
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    rw [hx]
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact smul_comm _ _ _

theorem exists_pow_smul_eq_zero_of_localizedModule_map_injective
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (φ : M →ₗ[R] Q) (f : R)
    (h : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ))
    (k : M) (hk : φ k = 0) : ∃ n : ℕ, f ^ n • k = 0 := by
  by_contra hne
  push_neg at hne
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M k)
  have hd : Disjoint (I : Set R) (Submonoid.powers f : Set R) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨n, rfl⟩
    exact hne n (by simpa [I] using ha)
  obtain ⟨P, hP, hIP, hPd⟩ := Ideal.exists_le_prime_disjoint I _ hd
  have hfP : f ∉ P := fun hf => Set.disjoint_left.1 hPd hf (Submonoid.mem_powers f)
  have h0 : LocalizedModule.map P.primeCompl φ (LocalizedModule.mk k 1) =
      LocalizedModule.map P.primeCompl φ 0 := by
    rw [LocalizedModule.map_mk, hk, LocalizedModule.zero_mk, map_zero]
  have h1 := h P hfP h0
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
  obtain ⟨u, hu⟩ := h1
  have hu' : (u : R) ∈ I := by
    simpa [I, Submonoid.smul_def] using hu
  exact u.2 (hIP hu')

theorem exists_embedding_bijective_localizedModule_map_of_rankAtStalk :
    ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
      (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ →
      (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R,
      ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers f)
          (Fintype.linearCombination R (b ∘ σ))) := by
  intro R Q _ _ _ _ _ N r b hspan hrank P₀
  let p := P₀.asIdeal
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.finitePresentation_of_projective _ _
  let v : Fin N → LocalizedModule p.primeCompl Q := fun i => LocalizedModule.mk (b i) 1
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ := by
    have hle : Submodule.span R (Set.range b) ≤
        ((Submodule.span (Localization.AtPrime p) (Set.range v)).restrictScalars R).comap
          (LocalizedModule.mkLinearMap p.primeCompl Q) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [eq_top_iff]
    rintro y -
    induction y using LocalizedModule.induction_on with
    | h q s =>
      have hq : LocalizedModule.mk q 1 ∈ Submodule.span (Localization.AtPrime p) (Set.range v) :=
        hle (hspan ▸ Submodule.mem_top)
      have : LocalizedModule.mk q s =
          (Localization.mk 1 s : Localization.AtPrime p) • LocalizedModule.mk q 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ hq
  obtain ⟨κ, a, bs, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  haveI : Finite κ := Module.Finite.finite_basis bs
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← hrank P₀, Module.rankAtStalk, Module.finrank_eq_card_basis bs]
  have ha : Function.Injective a := fun i j hij => bs.injective (by rw [hb, hb, hij])
  let eqv : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Fin r ↪ Fin N := eqv.toEmbedding.trans ⟨a, ha⟩
  let φ : (Fin r → R) →ₗ[R] Q := Fintype.linearCombination R (b ∘ σ)
  have hs0 : Function.Surjective (LocalizedModule.map p.primeCompl φ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← bs.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨LocalizedModule.mk (Pi.single (eqv.symm j) 1) 1, ?_⟩
    rw [LocalizedModule.map_mk, hb]
    simp [φ, σ, v]
  obtain ⟨f, hf, hfr⟩ := exists_smul_mem_range_of_surjective_localizedModule_map p φ hs0
  refine ⟨σ, f, hf, ?_,
    localizedModule_map_surjective_of_smul_mem_range _ φ f (Submonoid.mem_powers f) hfr⟩
  have hloc : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ) := by
    intro P hP hfP
    exact localizedModule_map_injective_of_surjective_of_rankAtStalk r ⟨P, hP⟩ (hrank ⟨P, hP⟩) φ
      (localizedModule_map_surjective_of_smul_mem_range _ φ f hfP hfr)
  rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    have hk : φ ((u : R) • (s : R) • x) = 0 := by
      simpa [Submonoid.smul_def, map_smul] using hu
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_localizedModule_map_injective φ f hloc _ hk
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨f ^ n, n, rfl⟩ * u, ?_⟩
    simp only [Submonoid.smul_def, smul_zero, Submonoid.coe_mul, mul_smul]
    exact hn

end GlobalTheory
