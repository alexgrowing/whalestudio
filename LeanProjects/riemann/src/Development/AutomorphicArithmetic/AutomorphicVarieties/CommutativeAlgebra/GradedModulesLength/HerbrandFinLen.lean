import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LengthQuotientSpanEqFinsumValuation
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.SnakeLen
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthExact
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open UpperTheory.V.abelian₂ (invLen coinvLen snake_len)
open scoped Pointwise

private theorem ker_range {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M] :
    LinearMap.ker (LinearMap.lsmul R M g) = Submodule.torsionBy R M g ∧
      LinearMap.range (LinearMap.lsmul R M g) = g • (⊤ : Submodule R M) := by
  constructor
  · ext x; simp
  · ext x
    simp [Submodule.mem_smul_pointwise_iff_exists]

private theorem theta_eq {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M] :
    theta g M = ((coinvLen g M).toNat : ℤ) - ((invLen g M).toNat : ℤ) := by
  unfold theta
  rw [(ker_range g M).1, (ker_range g M).2]
  rfl

private theorem herbrand_finLen {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    invLen g M ≠ ⊤ ∧ coinvLen g M ≠ ⊤ ∧ coinvLen g M = invLen g M := by
  have h1 := KStar.Selmer.length_ker_eq_length_coker (LinearMap.lsmul R M g) h
  rw [(ker_range g M).1, (ker_range g M).2] at h1
  have h2 : invLen g M ≠ ⊤ :=
    ne_top_of_le_ne_top h (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have h3 : coinvLen g M = invLen g M := h1.symm
  exact ⟨h2, h3 ▸ h2, h3⟩

private theorem herbrand_equiv {R : Type} [CommRing R] (g : R) {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    invLen g M = invLen g N ∧ coinvLen g M = coinvLen g N := by
  have key : ∀ {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N),
      invLen g M ≤ invLen g N ∧ coinvLen g N ≤ coinvLen g M := by
    intro M N _ _ _ _ e
    refine ⟨?_, ?_⟩
    · exact (snake_len R g M N PUnit e.toLinearMap 0 e.injective (fun _ => ⟨0, rfl⟩)
        (fun y => ⟨fun _ => e.surjective y, fun _ => rfl⟩)).2.2.2.1
    · exact (snake_len R g PUnit M N 0 e.toLinearMap (fun _ _ _ => rfl) e.surjective
        (fun y => ⟨fun h => ⟨0, (e.map_eq_zero_iff.1 h).symm⟩, by
          rintro ⟨_, rfl⟩; simp⟩)).2.2.2.2.1
  exact ⟨le_antisymm (key e).1 (key e.symm).1, le_antisymm (key e.symm).2 (key e).2⟩

private theorem loc_self {S : Type} [CommRing S] (P Q : Ideal S) [hP : P.IsPrime] (h : Q = P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (S ⧸ Q)) = 1 := by
  subst h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  constructor
  · rw [← not_subsingleton_iff_nontrivial, LocalizedModule.subsingleton_iff]
    intro h
    obtain ⟨r, hr, hr'⟩ := h (Submodule.Quotient.mk 1)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hr'
    exact hr (by simpa using hr')
  · intro x hx y
    induction x using LocalizedModule.induction_on with | h m s => ?_
    induction y using LocalizedModule.induction_on with | h m' s' => ?_
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective Q m
    obtain ⟨r', rfl⟩ := Submodule.Quotient.mk_surjective Q m'
    have hr : r ∈ Q.primeCompl := fun hr => hx (by
      rw [(Submodule.Quotient.mk_eq_zero Q).2 hr, LocalizedModule.zero_mk])
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * s'), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submonoid.coe_mul]
    congr 1
    ring

private theorem loc_not_le {S : Type} [CommRing S] (P Q : Ideal S) [hP : P.IsPrime] (h : ¬ Q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (S ⧸ Q)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp h
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Q x
  refine ⟨s, hs', ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Q.mul_mem_right _ hs

private theorem len_eq (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B]
    (X : Type) [AddCommGroup X] [Module O X] [Module B X] [IsScalarTower O B X] :
    Module.length O X = Module.length B X := by
  rw [IsLocalRing.length_restrictScalars O B X]
  have : Module.length (ResidueField O) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective (S := ResidueField O) (R := ResidueField B) (resMap_bijective O B).2]
    exact Module.length_eq_one _ _
  rw [this, mul_one]

private theorem prime_case (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ) (hv : IsNVal O K v)
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (P : Ideal B) [P.IsPrime] [Module.Finite O (B ⧸ P)]
    (a : B) (S : Finset (B →ₐ[O] K)) (hS : ∀ σ ∈ S, σ a ≠ 0) (hS' : ∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ (B ⧸ P) = 0) :
    invLen a (B ⧸ P) ≠ ⊤ ∧ coinvLen a (B ⧸ P) ≠ ⊤ ∧
      ((coinvLen a (B ⧸ P)).toNat : ℝ) - ((invLen a (B ⧸ P)).toNat : ℝ) =
        ∑ σ ∈ S, ((locLen σ (B ⧸ P)).toNat : ℝ) * v (σ a) := by
  classical
  have h0 : ∀ σ : B →ₐ[O] K, ¬ P ≤ RingHom.ker σ → locLen σ (B ⧸ P) = 0 := fun σ h =>
    haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
    loc_not_le _ P h
  by_cases hinj : P.comap (algebraMap O B) = ⊥
  · haveI : FaithfulSMul O (B ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
      intro c hc
      have : c ∈ P.comap (algebraMap O B) := by
        rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
        exact hc
      rwa [hinj] at this
    have hτ : ∀ τ : (B ⧸ P) →ₐ[O] K, Function.Injective τ := fun τ => by
      rw [RingHom.injective_iff_ker_eq_bot]
      refine Ideal.eq_bot_of_comap_eq_bot (R := O) ?_
      rw [eq_bot_iff]
      intro c hc
      have : τ (algebraMap O _ c) = 0 := hc
      rw [AlgHom.commutes] at this
      exact (FaithfulSMul.algebraMap_injective O K) (this.trans (map_zero _).symm)
    have h1 : ∀ τ : (B ⧸ P) →ₐ[O] K, locLen (τ.comp (Ideal.Quotient.mkₐ O P)) (B ⧸ P) = 1 := fun τ => by
      haveI : (RingHom.ker (τ.comp (Ideal.Quotient.mkₐ O P))).IsPrime := RingHom.ker_isPrime _
      refine loc_self _ P ?_
      ext x
      rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, AlgHom.comp_apply, map_eq_zero_iff _ (hτ τ)]
      rfl
    have hmem : ∀ τ : (B ⧸ P) →ₐ[O] K, τ.comp (Ideal.Quotient.mkₐ O P) ∈ S := fun τ => by
      by_contra h
      exact one_ne_zero ((h1 τ).symm.trans (hS' _ h))
    have ha : Ideal.Quotient.mk P a ≠ 0 := fun h =>
      hS _ (hmem (IsAlgClosed.lift (R := O) (S := B ⧸ P) (M := K))) (by
        rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, h, map_zero])
    obtain ⟨hf, hne, heq⟩ := length_quotient_span_eq_finsum_valuation O K v hv (B ⧸ P) _ ha
    have hi : invLen a (B ⧸ P) = 0 := by
      have : Submodule.torsionBy B (B ⧸ P) a = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : Ideal.Quotient.mk P a * x = 0 := (Submodule.mem_torsionBy_iff _ _).1 hx
        exact (mul_eq_zero.1 hx').resolve_left ha
      unfold invLen
      rw [this]
      exact Module.length_bot
    have hc : coinvLen a (B ⧸ P) = Module.length O ((B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P a}) := by
      rw [len_eq O B]
      have : a • (⊤ : Submodule B (B ⧸ P)) = (Ideal.span {Ideal.Quotient.mk P a}).restrictScalars B := by
        ext x
        rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
        constructor
        · rintro ⟨b, -, rfl⟩
          exact ⟨b, mul_comm _ _⟩
        · rintro ⟨b, rfl⟩
          exact ⟨b, trivial, mul_comm (Ideal.Quotient.mk P a) b⟩
      exact ((Submodule.quotEquivOfEq _ _ this).trans (Submodule.Quotient.restrictScalarsEquiv B _)).length_eq
    refine ⟨by simp [hi], hc ▸ hne, ?_⟩
    haveI := Fintype.ofFinite ((B ⧸ P) →ₐ[O] K)
    rw [hi, hc, heq, finsum_eq_sum_of_fintype]
    simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero]
    refine Finset.sum_of_injOn (fun τ => τ.comp (Ideal.Quotient.mkₐ O P)) ?_ (fun τ _ => hmem τ) ?_ ?_
    · intro τ _ τ' _ h
      exact Ideal.Quotient.algHom_ext O h
    · intro σ _ hσ
      rw [h0 σ fun hle => hσ ⟨Ideal.Quotient.liftₐ P σ hle, by simp, by ext; rfl⟩]
      simp
    · intro τ _
      rw [h1]
      simp
  · have hmax : P.IsMaximal := by
      haveI : (P.comap (algebraMap O B)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime hinj (Ideal.comap_isPrime _ _)
      haveI : (Ideal.comap (algebraMap O (B ⧸ P)) ⊥).IsMaximal := by
        convert this using 1
        ext x
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
        rfl
      have := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) (⊥ : Ideal (B ⧸ P)) this
      exact Ideal.Quotient.maximal_of_isField _ (Ring.isField_iff_maximal_bot.2 this)
    haveI : IsSimpleModule B (B ⧸ P) := isSimpleModule_iff_quot_maximal.mpr ⟨P, hmax, ⟨LinearEquiv.refl _ _⟩⟩
    obtain ⟨h1, h2, h3⟩ := herbrand_finLen a (B ⧸ P) (by rw [Module.length_eq_one]; simp)
    refine ⟨h1, h2, ?_⟩
    rw [h3, sub_self]
    refine (Finset.sum_eq_zero fun σ _ => ?_).symm
    rw [h0 σ fun hle => hinj ?_]
    · simp
    · rw [eq_bot_iff]
      intro c hc
      have : σ (algebraMap O B c) = 0 := hle hc
      rw [AlgHom.commutes] at this
      exact (FaithfulSMul.algebraMap_injective O K) (this.trans (map_zero _).symm)

theorem UpperTheory.V.Alg.M.th_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
      Module.Finite O (B ⧸ Module.annihilator B M) → ∀ (a : B) (S : Finset (B →ₐ[O] K)) (c : ℕ),
      (∀ σ ∈ S, σ a ≠ 0 ∧ 0 ≤ v (σ a) ∧ locLen σ M ≤ c) → (∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ M = 0) →
      (theta a M : ℝ) ≤ c * ∑ σ ∈ S, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv B _ _ _ M _ _ hM hfin a S c hS hS'
  have key : ∀ (I : Ideal B), Module.Finite O (B ⧸ I) → ∀ (N : Type) [AddCommGroup N] [Module B N]
      [hN : Module.Finite B N], I ≤ Module.annihilator B N → (∀ σ ∈ S, locLen σ N ≠ ⊤) →
      (∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ N = 0) →
      invLen a N ≠ ⊤ ∧ coinvLen a N ≠ ⊤ ∧ ((coinvLen a N).toNat : ℝ) - ((invLen a N).toNat : ℝ) =
        ∑ σ ∈ S, ((locLen σ N).toNat : ℝ) * v (σ a) := by
    intro I hI N _ _ hN
    induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B with
    | subsingleton N =>
      intro _ _ _
      obtain ⟨h1, h2, h3⟩ := herbrand_finLen a N (by simp)
      refine ⟨h1, h2, ?_⟩
      rw [h3, sub_self]
      refine (Finset.sum_eq_zero fun σ _ => ?_).symm
      have : locLen σ N = 0 := by
        unfold locLen
        exact Module.length_eq_zero
      simp [this]
    | quotient N p e =>
      intro hle _ h0
      have hl : ∀ σ : B →ₐ[O] K, locLen σ N = locLen σ (B ⧸ p.1) := fun σ =>
        GlobalTheory.length_localizedModule_congr _ e
      have hle' : I ≤ p.1 := by
        rw [e.annihilator_eq, Ideal.annihilator_quotient] at hle
        exact hle
      haveI : Module.Finite O (B ⧸ p.1) :=
        Module.Finite.of_surjective (Ideal.Quotient.factorₐ O hle').toLinearMap (Ideal.Quotient.factor_surjective hle')
      rw [(herbrand_equiv a e).1, (herbrand_equiv a e).2]
      simp only [hl] at h0 ⊢
      exact prime_case O K v hv B p.1 a S (fun σ h => (hS σ h).1) h0
    | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
      intro hle ht h0
      have hl : ∀ σ : B →ₐ[O] K, locLen σ N₂ = locLen σ N₁ + locLen σ N₃ := fun σ =>
        GlobalTheory.length_localizedModule_eq_add_of_exact _ f g hf hg hfg
      have ht1 : ∀ σ ∈ S, locLen σ N₁ ≠ ⊤ := fun σ h h' => ht σ h (by rw [hl, h', top_add])
      have ht3 : ∀ σ ∈ S, locLen σ N₃ ≠ ⊤ := fun σ h h' => ht σ h (by rw [hl, h', add_top])
      obtain ⟨a1, b1, c1⟩ := ih₁ (hle.trans (f.annihilator_le_of_injective hf)) ht1
        fun σ h => (add_eq_zero.1 ((hl σ).symm.trans (h0 σ h))).1
      obtain ⟨a3, b3, c3⟩ := ih₃ (hle.trans (g.annihilator_le_of_surjective hg)) ht3
        fun σ h => (add_eq_zero.1 ((hl σ).symm.trans (h0 σ h))).2
      obtain ⟨s1, s2, s3, -⟩ := snake_len B a N₁ N₂ N₃ f g hf hg hfg
      have a2 : invLen a N₂ ≠ ⊤ := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨a1, a3⟩) s2
      have b2 : coinvLen a N₂ ≠ ⊤ := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨b1, b3⟩) s3
      refine ⟨a2, b2, ?_⟩
      have s := congrArg (fun x : ℕ∞ => (x.toNat : ℝ)) s1
      have t1 : invLen a N₁ + invLen a N₃ ≠ ⊤ := WithTop.add_ne_top.2 ⟨a1, a3⟩
      have t2 : invLen a N₂ + coinvLen a N₁ ≠ ⊤ := WithTop.add_ne_top.2 ⟨a2, b1⟩
      rw [ENat.toNat_add t1 b2, ENat.toNat_add a1 a3, ENat.toNat_add t2 b3, ENat.toNat_add a2 b1] at s
      push_cast at s
      have : ∑ σ ∈ S, ((locLen σ N₂).toNat : ℝ) * v (σ a) =
          ∑ σ ∈ S, ((locLen σ N₁).toNat : ℝ) * v (σ a) + ∑ σ ∈ S, ((locLen σ N₃).toNat : ℝ) * v (σ a) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ h => ?_
        rw [hl, ENat.toNat_add (ht1 σ h) (ht3 σ h)]
        push_cast
        ring
      linarith
  obtain ⟨-, -, h⟩ := key _ hfin M le_rfl
    (fun σ h => ne_top_of_le_ne_top (ENat.coe_ne_top c) (hS σ h).2.2) hS'
  rw [theta_eq]
  push_cast
  rw [h, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ h => mul_le_mul_of_nonneg_right ?_ (hS σ h).2.1
  exact_mod_cast ENat.toNat_le_of_le_coe (hS σ h).2.2
