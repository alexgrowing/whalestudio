import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqRangeAddRange

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module PrimeSpectrum
open scoped Pointwise

universe u v

section Noeth

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

theorem length_quot_prime_ne_top_iff (q : Ideal A) [q.IsPrime] :
    length A (A ⧸ q) ≠ ⊤ ↔ q.IsMaximal := by
  constructor
  · intro h
    haveI : IsArtinian A (A ⧸ q) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
    apply Ideal.Quotient.maximal_of_isField
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A ⧸ q)
    refine ⟨y, ?_⟩
    have hxn : (Ideal.Quotient.mk q x) ^ n ≠ 0 := pow_ne_zero _ ha
    apply mul_left_cancel₀ hxn
    rw [mul_one, ← mul_assoc, ← pow_succ]
    first
      | simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hy
      | (rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow,
          mul_one] at hy; exact hy)
  · intro hq
    have hs : IsSimpleModule A (A ⧸ q) := isSimpleModule_iff_isCoatom.2 hq.out
    rw [Module.length_eq_one_iff.2 hs]
    first | exact ENat.one_ne_top | simp | decide

theorem length_ne_top_iff_support (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] :
    length A N ≠ ⊤ ↔ ∀ p ∈ support A N, p.asIdeal.IsMaximal := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := A) ‹_›
    (motive := fun N _ _ _ => length A N ≠ ⊤ ↔ ∀ p ∈ support A N, p.asIdeal.IsMaximal) ?_ ?_ ?_
  · intro N _ _ _ _
    simp [Module.length_eq_zero, Module.support_eq_empty]
  · intro N _ _ _ q e
    rw [e.length_eq, e.support_eq, length_quot_prime_ne_top_iff]
    have hs : support A (A ⧸ q.asIdeal) = zeroLocus (q.asIdeal : Set A) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    rw [hs]
    constructor
    · intro hq p hp
      rw [mem_zeroLocus, SetLike.coe_subset_coe] at hp
      rw [← hq.eq_of_le p.isPrime.ne_top hp]
      exact hq
    · intro h
      exact h q (by simp)
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hex h1 h3
    rw [Module.length_eq_add_of_exact f g hf hg hex, Module.support_of_exact hex hf hg]
    rw [show length A N₁ + length A N₃ ≠ ⊤ ↔ length A N₁ ≠ ⊤ ∧ length A N₃ ≠ ⊤ from
      WithTop.add_ne_top, h1, h3]
    simp only [Set.mem_union]
    constructor
    · rintro ⟨a, b⟩ p (hp | hp)
      exacts [a p hp, b p hp]
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

theorem range_lsmul_eq (N : Type v) [AddCommGroup N] [Module A N] (x : A) :
    LinearMap.range (LinearMap.lsmul A N x) = x • (⊤ : Submodule A N) := by
  ext m
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]

theorem support_coker (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] (x : A) :
    support A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) = support A N ∩ zeroLocus {x} := by
  rw [← Module.support_quotSMulTop]
  exact (Submodule.quotEquivOfEq _ _ (range_lsmul_eq N x)).support_eq

end Noeth

section Loc

variable {A : Type u} [CommRing A]

noncomputable def locLen (N : Type v) [AddCommGroup N] [Module A N] (p : PrimeSpectrum A) : ℕ∞ :=
  length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N)

theorem locLen_add {N₁ N₂ N₃ : Type v} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (p : PrimeSpectrum A) : locLen N₂ p = locLen N₁ p + locLen N₃ p := by
  unfold locLen
  refine Module.length_eq_add_of_exact (LocalizedModule.map p.asIdeal.primeCompl f)
    (LocalizedModule.map p.asIdeal.primeCompl g) ?_ ?_ ?_
  · first
      | exact LocalizedModule.map_injective _ _ hf
      | exact LocalizedModule.map_injective _ f hf
      | exact LocalizedModule.map_injective hf
  · first
      | exact LocalizedModule.map_surjective _ _ hg
      | exact LocalizedModule.map_surjective _ g hg
      | exact LocalizedModule.map_surjective hg
  · first
      | exact LocalizedModule.map_exact _ _ _ hex
      | exact LocalizedModule.map_exact _ f g hex
      | exact LocalizedModule.map_exact hex

theorem locLen_eq_zero_of_notMem {N : Type v} [AddCommGroup N] [Module A N] (p : PrimeSpectrum A)
    (hp : p ∉ support A N) : locLen N p = 0 := by
  unfold locLen
  have hs : Subsingleton (LocalizedModule p.asIdeal.primeCompl N) := by
    first
      | exact Module.notMem_support_iff.1 hp
      | exact Module.not_mem_support_iff.1 hp
  exact Module.length_eq_zero_iff.2 hs

theorem locLen_self {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) : locLen N q = 1 := by
  have key : ∀ (n : N) (s : q.asIdeal.primeCompl), LocalizedModule.mk n s = 0 → n = 0 := by
    intro n s h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    simp only [one_smul, smul_zero] at hu
    have h2 : (u : A) • e n = 0 := by rw [← map_smul, Submonoid.smul_def] at *; rw [hu, map_zero]
    rw [Algebra.smul_def, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (Ideal.Quotient.eq_zero_iff_mem.mp h2) u.2
    · simpa using h2
  have : IsSimpleModule (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl N) := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨⟨LocalizedModule.mk (e.symm 1) 1, 0, fun h => ?_⟩, ?_⟩
    · have := congrArg e (key _ _ h)
      simp at this
    · intro y hy z
      induction y using LocalizedModule.induction_on with
      | h n s =>
      induction z using LocalizedModule.induction_on with
      | h n' t =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e n)
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e n')
      have haq : a ∉ q.asIdeal := by
        intro h
        apply hy
        have : n = 0 := e.injective (by rw [← ha, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h)
        rw [this, LocalizedModule.zero_mk]
      refine ⟨Localization.mk (b * s) ⟨a * t, q.asIdeal.primeCompl.mul_mem haq t.2⟩, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
      refine ⟨1, e.injective ?_⟩
      simp only [one_smul, map_smul, Submonoid.smul_def, Submonoid.coe_mul, ← ha, ← hb,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
      ring
  exact Module.length_eq_one _ _

end Loc

section Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem withBot_eq_one {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe e =>
    have h1' : e ≤ 1 := by exact_mod_cast h1
    have h0' : ¬ e ≤ 0 := fun h => h0 (by exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => exact absurd h1' (by simp)
    | coe n =>
      have a1 : n ≤ 1 := by exact_mod_cast h1'
      have a0 : ¬ n ≤ 0 := fun h => h0' (by exact_mod_cast h)
      have hn : n = 1 := by omega
      subst hn
      first | rfl | norm_cast | simp

theorem dim_quot_eq_one_iff (hdim : ringKrullDim A = 1) (q : Ideal A) [q.IsPrime] :
    ringKrullDim (A ⧸ q) = 1 ↔ ¬ q.IsMaximal := by
  constructor
  · intro h hq
    haveI := hq
    letI := Ideal.Quotient.field q
    have h0 : ringKrullDim (A ⧸ q) = 0 := ringKrullDim_eq_zero_of_field (A ⧸ q)
    rw [h0] at h
    first | exact zero_ne_one h | simp at h | exact absurd h (by decide)
  · intro hq
    apply withBot_eq_one
    · calc ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
            ringKrullDim_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
        _ = 1 := hdim
    · intro hle
      have hbot : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk q) ≠ ⊥ := by
        intro h
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h
        apply hq
        have hqm : q = IsLocalRing.maximalIdeal A :=
          le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h
        rw [hqm]
        exact IsLocalRing.maximalIdeal.isMaximal A
      have hprime : ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk q)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
      let P0 : PrimeSpectrum (A ⧸ q) := ⟨⊥, Ideal.bot_prime⟩
      let P1 : PrimeSpectrum (A ⧸ q) := ⟨_, hprime⟩
      have hlt : P0 < P1 := lt_of_le_of_ne (show P0 ≤ P1 from bot_le)
        (fun h => hbot (congrArg PrimeSpectrum.asIdeal h).symm)
      let s : LTSeries (PrimeSpectrum (A ⧸ q)) :=
        { length := 1
          toFun := ![P0, P1]
          step := fun i => by
            fin_cases i
            first | exact hlt | simpa using hlt }
      have hs : (s.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum (A ⧸ q)) := by
        first
          | exact Order.LTSeries.length_le_krullDim s
          | exact LTSeries.length_le_krullDim s
          | exact Order.length_le_krullDim s
      have hk : (s.length : WithBot ℕ∞) ≤ 0 := hs.trans hle
      have hlen : s.length = 1 := rfl
      rw [hlen] at hk
      have h1 : (1 : ℕ) ≤ 0 := by exact_mod_cast hk
      omega

theorem eq_of_not_max_of_le (hdim : ringKrullDim A = 1) {p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (hp : ¬ p.IsMaximal) (hqp : q ≤ p) : p = q := by
  by_contra hne
  let P : PrimeSpectrum A := ⟨p, inferInstance⟩
  let Q : PrimeSpectrum A := ⟨q, inferInstance⟩
  let M : PrimeSpectrum A := IsLocalRing.closedPoint A
  have hQP : Q < P := lt_of_le_of_ne (show Q ≤ P from hqp)
    (fun h => hne (congrArg PrimeSpectrum.asIdeal h).symm)
  have hPM : P < M := lt_of_le_of_ne
    (show P ≤ M from IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
    (fun h => hp (by
      have h' : p = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal h
      rw [h']
      exact IsLocalRing.maximalIdeal.isMaximal A))
  let s : LTSeries (PrimeSpectrum A) :=
    { length := 2
      toFun := ![Q, P, M]
      step := fun i => by
        fin_cases i
        · first | exact hQP | simpa using hQP
        · first | exact hPM | simpa using hPM }
  have hs : (s.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum A) := by
    first
      | exact Order.LTSeries.length_le_krullDim s
      | exact LTSeries.length_le_krullDim s
      | exact Order.length_le_krullDim s
  have hlen : s.length = 2 := by
    first | rfl | simp [s, RelSeries.snoc_length, RelSeries.singleton_length]
  have hk : Order.krullDim (PrimeSpectrum A) = 1 := hdim
  rw [hlen, hk] at hs
  have h2 : (2 : ℕ) ≤ 1 := by exact_mod_cast hs
  omega

theorem finite_dimOne (hdim : ringKrullDim A = 1) :
    {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}.Finite := by
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  refine (Set.Finite.preimage (fun a _ b _ h => PrimeSpectrum.ext h) hfin).subset ?_
  intro p hp
  have hp' : ¬ p.asIdeal.IsMaximal := (dim_quot_eq_one_iff hdim p.asIdeal).1 hp
  show p.asIdeal ∈ minimalPrimes A
  simp only [minimalPrimes, Ideal.minimalPrimes, Set.mem_setOf_eq]
  refine ⟨⟨p.isPrime, bot_le⟩, fun q hq hqp => ?_⟩
  haveI := hq.1
  exact (eq_of_not_max_of_le hdim hp' hqp).le

theorem finsum_dimOne_eq (hdim : ringKrullDim A = 1) (F : PrimeSpectrum A → ℕ∞) :
    ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1), F p =
      ∑ p ∈ (finite_dimOne hdim).toFinset, F p := by
  exact finsum_mem_eq_finite_toFinset_sum F (finite_dimOne hdim)

end Local

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem support_of_equiv {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) : support A N = zeroLocus (q.asIdeal : Set A) := by
  haveI : Module.Finite A N := Module.Finite.equiv e.symm
  rw [Module.support_eq_zeroLocus, e.annihilator_eq, Ideal.annihilator_quotient]

theorem length_coker_equiv {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (e : N ≃ₗ[A] N') (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (N' ⧸ LinearMap.range (LinearMap.lsmul A N' x)) := by
  refine (Submodule.Quotient.equiv _ _ e ?_).length_eq
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨e m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨x • e.symm m, ⟨e.symm m, rfl⟩, by simp⟩

theorem length_coker_quot (q : PrimeSpectrum A) (x : A) :
    length A ((A ⧸ q.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) x)) =
      ordMod q x := by
  have hr : LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) x) =
      (Ideal.span {Ideal.Quotient.mk q.asIdeal x}).restrictScalars A := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]⟩
  rw [(Submodule.quotEquivOfEq _ _ hr).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A _).length_eq,
    Module.length_eq_of_surjective (S := A) (R := A ⧸ q.asIdeal) Ideal.Quotient.mk_surjective]
  rfl

theorem length_ker_quot_eq_zero {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) {x : A} (hx : x ∉ q.asIdeal) :
    length A (LinearMap.ker (LinearMap.lsmul A N x)) = 0 := by
  have hsub : Subsingleton (LinearMap.ker (LinearMap.lsmul A N x)) := by
    refine ⟨fun a b => ?_⟩
    suffices h : ∀ c : LinearMap.ker (LinearMap.lsmul A N x), c = 0 by rw [h a, h b]
    intro c
    obtain ⟨n, hn⟩ := c
    have hn' : x • n = 0 := hn
    apply Subtype.ext
    show n = 0
    have h1 : x • e n = 0 := by rw [← map_smul, hn', map_zero]
    have h2 : e n = 0 := by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e n)
      rw [← ha] at h1 ⊢
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem] at h1
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (q.isPrime.mem_or_mem h1).resolve_left hx
    exact e.injective (by rw [h2, map_zero])
  exact Module.length_eq_zero_iff.2 hsub

end Main

section Final

theorem enat_step {k1 k3 c2 k2 c1 c3 s1 s3 : ℕ∞} (h1 : k1 ≠ ⊤) (h3 : k3 ≠ ⊤) (hc1 : c1 ≠ ⊤)
    (hc3 : c3 ≠ ⊤) (hc2 : c2 ≠ ⊤) (e1 : c1 = k1 + s1) (e3 : c3 = k3 + s3)
    (eu : k1 + k3 + c2 = k2 + c1 + c3) : k2 ≠ ⊤ ∧ c2 = k2 + (s1 + s3) := by
  have hs1 : s1 ≠ ⊤ := by
    rintro rfl
    rw [add_top] at e1
    exact hc1 e1
  have hs3 : s3 ≠ ⊤ := by
    rintro rfl
    rw [add_top] at e3
    exact hc3 e3
  have hk2 : k2 ≠ ⊤ := by
    rintro rfl
    rw [top_add, top_add] at eu
    lift k1 to ℕ using h1
    lift k3 to ℕ using h3
    lift c2 to ℕ using hc2
    exact absurd eu (by simp)
  refine ⟨hk2, ?_⟩
  lift k1 to ℕ using h1
  lift k3 to ℕ using h3
  lift s1 to ℕ using hs1
  lift s3 to ℕ using hs3
  lift k2 to ℕ using hk2
  lift c2 to ℕ using hc2
  subst e1 e3
  norm_cast at eu ⊢
  omega

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

noncomputable def dimOneSum (N : Type v) [AddCommGroup N] [Module A N] (x : A) : ℕ∞ :=
  ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1), locLen N p * ordMod p x

theorem length_coker_eq_ker_add_dimOneOrderSum (hdim : ringKrullDim A = 1) (x : A) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    (∀ p ∈ support A M, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
      length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
        length A (LinearMap.ker (LinearMap.lsmul A M x)) + dimOneSum M x := by
  have hc : ∀ (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N],
      (∀ p ∈ support A N, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) ≠ ⊤ := by
    intro N _ _ _ H
    rw [length_ne_top_iff_support, support_coker]
    rintro p ⟨hp, hx⟩
    exact H p hp (by simpa [mem_zeroLocus] using hx)
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := A) ‹_›
    (motive := fun N _ _ _ => (∀ p ∈ support A N, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (LinearMap.ker (LinearMap.lsmul A N x)) ≠ ⊤ ∧
      length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
        length A (LinearMap.ker (LinearMap.lsmul A N x)) + dimOneSum N x) ?_ ?_ ?_
  · intro N _ _ _ _ _
    have h0 : dimOneSum N x = 0 := by
      rw [dimOneSum, finsum_dimOne_eq hdim]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [locLen_eq_zero_of_notMem p (by simp [Module.support_eq_empty]), zero_mul]
    simp [h0, Module.length_eq_zero]
  · intro N _ _ _ q e H
    have hsupp := support_of_equiv q e
    by_cases hq : q.asIdeal.IsMaximal
    · have hN : length A N ≠ ⊤ := by
        rw [e.length_eq]; exact (length_quot_prime_ne_top_iff q.asIdeal).mpr hq
      have h0 : dimOneSum N x = 0 := by
        rw [dimOneSum, finsum_dimOne_eq hdim]
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim] at hp
        rw [locLen_eq_zero_of_notMem p, zero_mul]
        intro hp'
        rw [hsupp, mem_zeroLocus, SetLike.coe_subset_coe] at hp'
        exact hp (by rw [← hq.eq_of_le p.isPrime.ne_top hp']; exact hq)
      refine ⟨ne_top_of_le_ne_top hN (Module.length_le_of_injective _ (Submodule.injective_subtype _)), ?_⟩
      rw [euler_finLength hN x, h0, add_zero]
    · have hx : x ∉ q.asIdeal := fun hx => hq (H q (by rw [hsupp]; simp) hx)
      have hs : dimOneSum N x = ordMod q x := by
        rw [dimOneSum, finsum_dimOne_eq hdim, Finset.sum_eq_single q, locLen_self q e, one_mul]
        · intro p hp hpq
          rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim] at hp
          rw [locLen_eq_zero_of_notMem p, zero_mul]
          intro hp'
          rw [hsupp, mem_zeroLocus, SetLike.coe_subset_coe] at hp'
          exact hpq (PrimeSpectrum.ext (eq_of_not_max_of_le hdim hp hp'))
        · intro hq'
          exact absurd (by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim]; exact hq) hq'
      rw [length_ker_quot_eq_zero q e hx, hs, length_coker_equiv e x, length_coker_quot, zero_add]
      exact ⟨by simp, rfl⟩
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hex h1 h3 H
    have H1 : ∀ p ∈ support A N₁, x ∈ p.asIdeal → p.asIdeal.IsMaximal := fun p hp =>
      H p (Module.support_subset_of_injective f hf hp)
    have H3 : ∀ p ∈ support A N₃, x ∈ p.asIdeal → p.asIdeal.IsMaximal := fun p hp =>
      H p (Module.support_subset_of_surjective g hg hp)
    obtain ⟨k1, e1⟩ := h1 H1
    obtain ⟨k3, e3⟩ := h3 H3
    have hs : dimOneSum N₂ x = dimOneSum N₁ x + dimOneSum N₃ x := by
      simp only [dimOneSum, finsum_dimOne_eq hdim, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [locLen_add f g hf hg hex p, add_mul]
    rw [hs]
    exact enat_step k1 k3 (hc N₁ H1) (hc N₃ H3) (hc N₂ H) e1 e3 (euler_ses f g hf hg hex x)

end Final

theorem dimOneFormula : LocalLengthAdditivity := by
  unfold LocalLengthAdditivity
  intro A _ _ _ M _ _ _ x hdim hfin
  have h := (length_ne_top_iff_support (M ⧸ LinearMap.range (LinearMap.lsmul A M x))).1 hfin
  rw [support_coker] at h
  exact length_coker_eq_ker_add_dimOneOrderSum hdim x M (fun p hp hx =>
    h p ⟨hp, (PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 hx)⟩)

end ReciprocityTheory.ChartRestriction.G.AI
