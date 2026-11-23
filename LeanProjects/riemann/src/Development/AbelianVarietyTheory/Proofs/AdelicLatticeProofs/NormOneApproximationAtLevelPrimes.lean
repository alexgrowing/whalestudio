import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationEqOneOfNormOneOfNotMoved
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.NormOne

lemma exists_split (N : ℕ) : ∀ M : ℕ, 0 < M → ∃ D₁ D₂ k : ℕ, M = D₁ * D₂ ∧ D₁ ∣ N ^ k ∧ D₂.Coprime N := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h : M.Coprime N
    · exact ⟨1, M, 0, by simp, by simp, h⟩
    · obtain ⟨M', hM'⟩ := Nat.gcd_dvd_left M N
      have hg : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left N hM
      have hg1 : Nat.gcd M N ≠ 1 := h
      have hpos : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with h0 | h0
        · rw [h0, mul_zero] at hM'; omega
        · exact h0
      have hlt : M' < M := by
        have h2 : 2 ≤ Nat.gcd M N := by omega
        nlinarith
      obtain ⟨D₁, D₂, k, h1, h2, h3⟩ := ih M' hlt hpos
      refine ⟨Nat.gcd M N * D₁, D₂, k + 1, by rw [mul_assoc, ← h1]; exact hM', ?_, h3⟩
      rw [pow_succ']
      exact Nat.mul_dvd_mul (Nat.gcd_dvd_right M N) h2

variable {E : Type} [Field E] [NumberField E]

lemma exists_nat_multiple (α : 𝓞 E) (h : α ≠ 0) : ∃ n : ℕ, 0 < n ∧ ∃ γ : 𝓞 E, (n : 𝓞 E) = α * γ := by
  refine ⟨Ideal.absNorm (Ideal.span {α}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

lemma one_add_ne_zero (N : ℕ) (hN : N ≠ 1) (z : 𝓞 E) : 1 + (N : 𝓞 E) * z ≠ 0 := by
  intro h
  have hu : IsUnit (N : 𝓞 E) := IsUnit.of_mul_eq_one (-z) (by linear_combination -h)
  have h2 := hu.map (Algebra.norm ℤ)
  have h3 : (N : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ) := by simp
  rw [h3, Algebra.norm_algebraMap, isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne',
    Int.isUnit_iff] at h2
  omega

lemma exists_coprime_multiple (N : ℕ) (hN : 0 < N) (z : 𝓞 E) (hw : 1 + (N : 𝓞 E) * z ≠ 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∃ γ : 𝓞 E, (t : 𝓞 E) = (1 + (N : 𝓞 E) * z) * γ := by
  set I : Ideal (𝓞 E) := Ideal.span {1 + (N : 𝓞 E) * z} with hI
  have hb : I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hw
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hb
  have h0 : Ideal.Quotient.mk I (1 + (N : 𝓞 E) * z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hu : IsUnit (Ideal.Quotient.mk I (N : 𝓞 E)) :=
    IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (-z)) (by
      rw [map_add, map_one, map_mul] at h0
      rw [map_neg]; linear_combination -h0)
  obtain ⟨v, hv⟩ := hu
  obtain ⟨k, hk, hvk⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite v)
  have h1 : 1 ≤ N ^ k := Nat.one_le_pow _ _ hN
  refine ⟨N ^ k - 1, ?_, ?_⟩
  · have : (N ^ k - 1).Coprime (N ^ k) := by
      have := (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left _)
      exact this
    exact (Nat.coprime_pow_right_iff hk _ _).mp this
  · apply Ideal.mem_span_singleton.mp
    rw [← hI, ← Ideal.Quotient.eq_zero_iff_mem, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, map_sub,
      map_pow, ← hv, ← Units.val_pow_eq_pow_val, hvk]
    simp

lemma val_eq_one (P : HeightOneSpectrum (𝓞 E)) (d : 𝓞 E) (hd : d ∉ P.asIdeal) :
    P.valuation E (d : E) = 1 := by
  have h1 : P.valuation E (algebraMap (𝓞 E) E d) ≤ 1 := P.valuation_le_one d
  have h2 : ¬ P.valuation E (algebraMap (𝓞 E) E d) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hd
  exact le_antisymm h1 (not_lt.mp h2)

lemma val_le_of_mul (P : HeightOneSpectrum (𝓞 E)) (x y : E) (d : 𝓞 E) (hd : d ∉ P.asIdeal)
    (h : x * d = y) (hy : P.valuation E y ≤ 1) : P.valuation E x ≤ 1 := by
  rw [← h, map_mul, val_eq_one P d hd, mul_one] at hy
  exact hy

lemma val_le_of_unit (P : HeightOneSpectrum (𝓞 E)) (y : E) (D : ℕ) (hD : (D : 𝓞 E) ∉ P.asIdeal)
    (hy : P.valuation E y = 1) : P.valuation E ((y - 1) / D) ≤ 1 := by
  have hD0 : (D : E) ≠ 0 := by
    intro h
    have : D = 0 := by exact_mod_cast h
    apply hD; simp [this]
  refine val_le_of_mul P _ (y - 1) (D : 𝓞 E) hD (by simp [hD0]) ?_
  exact Valuation.map_sub_le _ hy.le (by simp)

lemma val_le_of_cong (P : HeightOneSpectrum (𝓞 E)) (N D D₁ D₂ k n : ℕ) (hD0 : 0 < D)
    (hM : D * n = D₁ * D₂) (h1 : D₁ ∣ N ^ k) (hN : (N : 𝓞 E) ∉ P.asIdeal) (hD : (D : 𝓞 E) ∈ P.asIdeal)
    (α β p b : 𝓞 E) (hab : p * D₂ + b = 1) :
    P.valuation E ((((p * D₂ * α + b : 𝓞 E) : E) / ((p * D₂ * β + b : 𝓞 E) : E) - 1) / D) ≤ 1 := by
  have hP := P.isPrime
  have hM' : (D : 𝓞 E) * n = D₁ * D₂ := by exact_mod_cast hM
  have hD₁ : (D₁ : 𝓞 E) ∉ P.asIdeal := by
    intro h
    obtain ⟨e, he⟩ := h1
    apply hN
    apply hP.mem_of_pow_mem k
    have : (N : 𝓞 E) ^ k = D₁ * e := by exact_mod_cast he
    rw [this]; exact Ideal.mul_mem_right _ _ h
  have hD₂ : (D₂ : 𝓞 E) ∈ P.asIdeal := by
    have : (D₁ : 𝓞 E) * D₂ ∈ P.asIdeal := hM' ▸ Ideal.mul_mem_right _ _ hD
    exact (hP.mem_or_mem this).resolve_left hD₁
  have hβ : p * D₂ * β + b ∉ P.asIdeal := by
    intro h
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (p * D₂ * β + b) + D₂ * (p * (1 - β)) := by linear_combination -hab
    rw [this]
    exact add_mem h (Ideal.mul_mem_right _ _ hD₂)
  have hβ0 : ((p * D₂ * β + b : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hβ
    have : (p * D₂ * β + b : 𝓞 E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD0.ne'
  have hME : (D : E) * n = D₁ * D₂ := by exact_mod_cast hM
  refine val_le_of_mul P _ ((n * p * (α - β) : 𝓞 E) : E) (D₁ * (p * D₂ * β + b))
    (fun h => (hP.mem_or_mem h).elim hD₁ hβ) ?_ (P.valuation_le_one _)
  rw [RingOfIntegers.coe_eq_algebraMap] at hβ0
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_sub, map_natCast] at hβ0 ⊢
  field_simp
  linear_combination (-(algebraMap (𝓞 E) E p) * (algebraMap (𝓞 E) E α - algebraMap (𝓞 E) E β)) * hME

variable {F : Type} [Field F] [Algebra F E]

omit [NumberField E] in
lemma exists_conj (c : E ≃ₐ[F] E) (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = c x :=
  ⟨⟨c x, (RingOfIntegers.isIntegral_coe x).map (c : E →+* E).toIntAlgHom⟩, rfl⟩

lemma hilbert90_matrix_subalgebra_norm_one (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) (u : E) (hu : u * c u = 1) :
    ∃ α : 𝓞 E, α ≠ 0 ∧ u * c α = α := by
  have h0 : ∃ x : E, x ≠ 0 ∧ u * c x = x := by
    have key : ∀ θ : E, u * c (θ + u * c θ) = θ + u * c θ := by
      intro θ
      rw [map_add, map_mul, hc]
      linear_combination θ * hu
    by_cases h : 1 + u * c 1 = 0
    · have : ∃ θ, c θ ≠ θ := by
        by_contra hh
        push Not at hh
        exact hc1 (AlgEquiv.ext hh)
      obtain ⟨θ, hθ⟩ := this
      refine ⟨_, ?_, key θ⟩
      rw [map_one] at h
      intro h2
      apply hθ
      linear_combination c θ * h - h2
    · exact ⟨_, h, key 1⟩
  obtain ⟨x, hx, hux⟩ := h0
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  obtain ⟨q', hq'⟩ := exists_conj c q
  have hq0 : (q : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hq
    exact_mod_cast this
  have hp : (p : E) = x * q := by
    rw [← hpq]; exact (div_mul_cancel₀ _ hq0).symm
  have e : ((p * q' : 𝓞 E) : E) = x * q * c q := by
    rw [← hp, ← hq']; rfl
  refine ⟨p * q', ?_, ?_⟩
  · intro h
    rw [h] at e
    have hcq : c q ≠ 0 := by simpa using hq0
    exact mul_ne_zero (mul_ne_zero hx hq0) hcq (e.symm.trans rfl)
  · rw [e, map_mul, map_mul, hc]
    linear_combination (c q * q) * hux

end GlobalTheory.UnRep.NormOne

open GlobalTheory.UnRep.NormOne in

theorem GlobalTheory.UnRep.normOne_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  intro F E _ _ _ _ _ c hc hc1 u N D hu hN hD
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨1, by simp, ⟨0, by simp, 0, by simp⟩, 1, ⟨one_ne_zero, fun P hP h => Or.inr (by simpa using h)⟩,
      ⟨0, by simp⟩, 0, by simp⟩
  obtain ⟨α, hα, huα⟩ := hilbert90_matrix_subalgebra_norm_one c hc hc1 u hu
  obtain ⟨β, hβc⟩ := exists_conj c α
  have hαE : (α : E) ≠ 0 := by exact_mod_cast hα
  have hβE : (β : E) ≠ 0 := by rw [hβc]; simpa using hαE
  have hβ : β ≠ 0 := by intro h; apply hβE; rw [h]; rfl
  obtain ⟨n₁, hn₁, γ₁, hγ₁⟩ := exists_nat_multiple α hα
  obtain ⟨n₂, hn₂, γ₂, hγ₂⟩ := exists_nat_multiple β hβ
  obtain ⟨D₁, D₂, k, hM, h1, h2⟩ := exists_split N (D * (n₁ * n₂)) (by positivity)
  have hco : D₂.Coprime (D₁ * N) :=
    Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k h2)) h2
  obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hco
  have hpq' : (p : 𝓞 E) * D₂ + q * (D₁ * N) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
  have hM' : (D : 𝓞 E) * (α * γ₁ * (β * γ₂)) = D₁ * D₂ := by
    rw [← hγ₁, ← hγ₂]; exact_mod_cast hM
  set b : 𝓞 E := q * (D₁ * N) with hb
  set α' : 𝓞 E := p * D₂ * α + b with hα'
  set β' : 𝓞 E := p * D₂ * β + b with hβ'
  have hcα' : c α' = β' := by
    simp only [hα', hβ', hb, RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_natCast, map_intCast] at hβc ⊢
    rw [hβc]
  have hcβ' : c β' = α' := by rw [← hcα', hc]
  set z : 𝓞 E := -2 * q * D₁ + q * D₁ * b + p * q * (D * α * γ₁ * γ₂) with hz
  have hw := one_add_ne_zero N hN1 z
  obtain ⟨t, ht, γ, hγ⟩ := exists_coprime_multiple N hN z hw
  have e1 : p * D₂ * β' = β * (1 + N * z) := by
    rw [hβ', hz, hb]
    linear_combination (β * (p * D₂ + 1 - q * (D₁ * N))) * hpq' - (p * q * N : 𝓞 E) * hM'
  have hβ'0 : β' ≠ 0 := by
    intro h
    rw [h, mul_zero] at e1
    exact mul_ne_zero hβ hw e1.symm
  have hβ'E : (β' : E) ≠ 0 := by exact_mod_cast hβ'0
  have hα'E : (α' : E) ≠ 0 := by rw [← hcβ']; simpa using hβ'E
  have hu' : (α' : E) / β' * c ((α' : E) / β') = 1 := by
    rw [map_div₀, hcα', hcβ']; field_simp
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨(α' : E) / β', hu', ⟨t, ht, γ * p * q * N * γ₁ * γ₂ * (β - α), ?_⟩, ?_⟩
  · have hu2 : u = (α : E) / β := by rw [eq_div_iff hβE, hβc, huα]
    have e2 : (t : 𝓞 E) * (α' * β - β' * α) = D * (γ * p * q * N * γ₁ * γ₂ * (β - α)) * (β' * α) := by
      apply mul_left_cancel₀ hβ
      have e3 : α' * β - β' * α = b * (β - α) := by rw [hα', hβ']; ring
      rw [e3, hγ, hb]
      linear_combination (-(γ * q * D₁ * N * (β - α))) * e1 - (γ * p * q * N * (β - α) * β') * hM'
    generalize γ * p * q * N * γ₁ * γ₂ * (β - α) = g at e2 ⊢
    have e4 := congrArg (algebraMap (𝓞 E) E) e2
    simp only [map_mul, map_sub, map_natCast] at e4
    rw [hu2]
    field_simp
    simp only [RingOfIntegers.coe_eq_algebraMap] at e4 ⊢
    linear_combination e4
  · have hM2 : D * (n₁ * n₂) = D₁ * D₂ := hM
    obtain ⟨s, hs0, hsP, hs⟩ := GlobalTheory.UnRep.exists_denominator_primes_prescribed E (fun P => Moved c P ∨ (N : 𝓞 E) ∈ P) Bool
      (fun i => if i then ((α' : E) / β' - 1) / D else (((α' : E) / β')⁻¹ - 1) / D) (by
        intro i P hQ
        rw [not_or] at hQ
        have hv := GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved F E c hc _ P hu' hQ.1
        by_cases hDP : (D : 𝓞 E) ∈ P.asIdeal
        · cases i
          · simp only [Bool.false_eq_true, if_false, inv_div]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP β α p b hpq'
          · simp only [if_true]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP α β p b hpq'
        · cases i
          · simp only [Bool.false_eq_true, if_false]
            exact val_le_of_unit P _ D hDP (by rw [map_inv₀, hv, inv_one])
          · simp only [if_true]
            exact val_le_of_unit P _ D hDP hv)
    obtain ⟨b₁, hb₁⟩ := hs true
    obtain ⟨b₂, hb₂⟩ := hs false
    simp only [if_true] at hb₁
    simp only [Bool.false_eq_true, if_false] at hb₂
    refine ⟨s, ⟨hs0, hsP⟩, ⟨b₁, ?_⟩, b₂, ?_⟩
    · rw [← hb₁, mul_left_comm, mul_div_cancel₀ _ hDE]
    · rw [← hb₂, mul_left_comm, mul_div_cancel₀ _ hDE]
