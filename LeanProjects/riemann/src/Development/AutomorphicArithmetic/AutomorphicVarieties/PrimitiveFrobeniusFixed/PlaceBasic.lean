import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.PlaceBasics

section Rat

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  have h : normV (vQ l) = Ideal.absNorm (vQ l).asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h]
  show Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

private theorem mem_vQ : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l).asIdeal := Ideal.mem_span_singleton_self _

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem not_of_coprime (A : ValuationSubring Ω) {m n : ℤ} (hc : IsCoprime m n)
    (hm : A.valuation (m : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨a, b, hab⟩ := hc
  have h1 : A.valuation ((a : Ω) * (m : Ω) + (b : Ω) * (n : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hm
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
  have h2 : (a : Ω) * (m : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    exact not_of_coprime A (((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd)
      (by rwa [Int.cast_natCast]) h
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

end Rat

section Roots

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

private theorem val_root {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem one_sub_pow {η : Ω} (h1 : A.valuation η = 1) (h : A.valuation (η - 1) < 1) (i : ℕ) :
    A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_eq_one {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1)
    (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => one_sub_pow A (val_root A hv hη) h i

private theorem root_eq {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ξ ζ : Ω} (hξ : ξ ^ m = 1) (hζ : ζ ^ m = 1)
    (h : A.valuation (ξ - ζ) < 1) : ξ = ζ := by
  have h1 := val_root A hv hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at h1
  have e : ξ / ζ - 1 = (ξ - ζ) / ζ := by field_simp
  have : ξ / ζ = 1 := by
    refine root_eq_one A hv (by rw [div_pow, hξ, hζ, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact h
  exact (div_eq_one_iff_eq h0).1 this

end Roots

section Conj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (g : G ℚ Ω)

private theorem smul_mem (y : Ω) : g y ∈ g • A ↔ y ∈ A := by
  rw [← AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

private theorem smul_le (y : Ω) : (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, smul_mem]

private theorem smul_lt (y : Ω) : (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', smul_mem, ← map_inv₀, smul_mem, map_eq_zero_iff _ g.injective]

private theorem smul_eq (y : Ω) : (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, smul_le, smul_lt]

private theorem dec_iff (x : G ℚ Ω) : x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A := by
  rw [mem_Dec, mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]

private theorem pow_iff (x : G ℚ Ω) (q : ℕ) :
    (∀ y : Ω, (g • A).valuation y ≤ 1 → (g • A).valuation (x y - y ^ q) < 1) ↔
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation ((g⁻¹ * x * g) y - y ^ q) < 1 := by
  rw [g.surjective.forall]
  refine forall_congr' fun y => ?_
  have e : x (g y) - g y ^ q = g ((g⁻¹ * x * g) y - y ^ q) := by
    rw [map_sub, map_pow, ← AlgEquiv.mul_apply g, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      AlgEquiv.mul_apply]
  rw [e, smul_le, smul_lt]

end Conj

end UpperTheory.V.ML.PlaceBasics

open UpperTheory.V.ML.PlaceBasics in
theorem UpperTheory.V.ML.placeBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ q : ℕ, q.Prime → ∃ A : ValuationSubring Ω, Over A q) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ φ : G ℚ Ω, IsFrob (F := ℚ) A q φ) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), Over A (m * n) ↔ Over A m ∨ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), m.Coprime n → Over A m → ¬ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ), ¬ Over A k → Ine (F := ℚ) A ≤ fixMu ℚ Ω k) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ) (ζ : Ω), ¬ Over A k → ζ ^ k = 1 → A.valuation (ζ - 1) < 1 → ζ = 1) ∧
    (∀ (A : ValuationSubring Ω) (q k : ℕ) (φ : G ℚ Ω), IsFrob (F := ℚ) A q φ → ¬ Over A k → Pows k q φ) ∧
    (∀ (A A' : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → Over A' q → ∃ g : G ℚ Ω, A' = g • A) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ normV v = q ∧ (q : 𝓞 ℚ) ∈ v.asIdeal) ∧
    ∀ (A : ValuationSubring Ω) (g : G ℚ Ω), (∀ x, x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A) ∧ (∀ x, x ∈ Ine (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Ine (F := ℚ) A) ∧
      (∀ q x, IsFrob (F := ℚ) (g • A) q x ↔ IsFrob (F := ℚ) A q (g⁻¹ * x * g)) ∧ (∀ y : Ω, (g • A).valuation (g y) < 1 ↔ A.valuation y < 1) ∧ ∀ y : Ω, (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  intro Ω _ _ _
  refine ⟨fun q hq => ?_, fun A q hq hA => ?_, fun A m n => ?_, fun A m n hc hm => ?_, fun A k hk g hg x hx => ?_,
    fun A k ζ hk hζ h => root_eq_one A hk hζ h, fun A q k φ hφ hk x hx => ?_, fun A A' q hq hA hA' => ?_,
    fun A q hq hA => ?_, fun A g => ⟨dec_iff A g, fun x => ?_, fun q x => and_congr (dec_iff A g x) (pow_iff A g x q),
      smul_lt A g, smul_eq A g⟩⟩
  · haveI := Fact.mk hq
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (vQ q)
    refine ⟨A, ?_⟩
    simpa using (hA ((q : ℕ) : 𝓞 ℚ)).2 (mem_vQ q)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_isFrob (isPlaceOver_vQ A hA)
    rw [normV_vQ] at hg
    exact ⟨g, hg⟩
  · have hm : A.valuation (m : Ω) ≤ 1 := by simpa using val_intCast_le_one A m
    have hn : A.valuation (n : Ω) ≤ 1 := by simpa using val_intCast_le_one A n
    simp only [Over, Nat.cast_mul, map_mul]
    refine ⟨fun h => ?_, fun h => h.elim (lt_of_le_of_lt (mul_le_of_le_one_right' hn))
      (lt_of_le_of_lt (mul_le_of_le_one_left' hm))⟩
    by_contra h'
    rw [not_or] at h'
    rw [hm.eq_of_not_lt h'.1, hn.eq_of_not_lt h'.2, one_mul] at h
    exact lt_irrefl _ h
  · have := not_of_coprime A (Nat.isCoprime_iff_coprime.2 hc) (by rwa [Int.cast_natCast])
    rwa [Int.cast_natCast] at this
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) hx (hg.2 x (val_root A hk hx).le)
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow])
      (hφ.2 x (val_root A hk hx).le)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
    exact ⟨g, hg.symm⟩
  · haveI := Fact.mk hq
    exact ⟨vQ q, isPlaceOver_vQ A hA, normV_vQ q, mem_vQ q⟩
  · have h := pow_iff A g x 1
    simp only [pow_one] at h
    exact and_congr (dec_iff A g x) h
