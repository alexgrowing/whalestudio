import Mathlib
import Formalism.PeriodIntegrals.OkpInert

open NumberField

noncomputable section

namespace PI.OkpW

theorem norm_le_one_of_integral {F R : Type*} [NormedField F] [IsUltrametricDist F] [CommRing R]
    [Algebra R F] (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) (δ : F) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨f, hf, hfe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one,
    one_mul] at hfe
  have h1 : δ ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hfe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ f.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ f.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R F (f.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ f.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ f.natDegree / ‖δ‖ < ‖δ‖ ^ f.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ f.natDegree‖ = ‖δ‖ ^ f.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_le_one_of_integral_int {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra ℤ F]
    (δ : F) (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral (fun n => by
    rw [eq_intCast (algebraMap ℤ F) n]; exact IsUltrametricDist.norm_intCast_le_one F n) δ h

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [this, norm_algebraMap', Padic.norm_p]

variable {K : Type} [Field K] [NumberField K]

theorem norm_tau_le (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
by
  have hI : IsIntegral ℤ (τ (a : K)) := by
    obtain ⟨f, hm, he⟩ := RingOfIntegers.isIntegral_coe a
    refine ⟨f, hm, ?_⟩
    have := congrArg τ he
    rw [Polynomial.hom_eval₂, map_zero] at this
    rwa [Subsingleton.elim (τ.comp (algebraMap ℤ K)) (algebraMap ℤ ℂ_[p])] at this
  exact norm_le_one_of_integral_int _ hI

theorem norm_tau_dvd (τ : K →+* ℂ_[p]) {a : 𝓞 K} {k : ℕ} (h : (p : 𝓞 K) ^ k ∣ a) :
    ‖τ (a : K)‖ ≤ (p : ℝ)⁻¹ ^ k := by
  obtain ⟨b, rfl⟩ := h
  have : τ (((p : 𝓞 K) ^ k * b : 𝓞 K) : K) = (p : ℂ_[p]) ^ k * τ (b : K) := by simp
  rw [this, norm_mul, norm_pow, norm_p_cp]
  exact mul_le_of_le_one_right (by positivity) (norm_tau_le τ b)

theorem span_p_ne_bot : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero

theorem isMaximal_span_p (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) :
    (Ideal.span {(p : 𝓞 K)}).IsMaximal :=
  hP.isMaximal span_p_ne_bot

theorem natCard_quot (hK : Module.finrank ℚ K = 2) :
    Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  have h := Ideal.absNorm_span_singleton (p : 𝓞 K)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h]
  have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
  simp

theorem finite_quot (hK : Module.finrank ℚ K = 2) : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quot hK]; exact (pow_pos hp.out.pos 2).ne')

theorem pow_q_sub (hK : Module.finrank ℚ K = 2) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (a : 𝓞 K) (n : ℕ) : (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  haveI := finite_quot (K := K) (p := p) hK
  letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
  have hc : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot hK]
  rw [map_pow, ← hc, FiniteField.pow_card_pow]

theorem exists_inv_mod (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K} (ha : ¬ (p : 𝓞 K) ∣ a) :
    ∃ b : 𝓞 K, (p : 𝓞 K) ∣ a * b - 1 := by
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  have h0 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a)⁻¹
  refine ⟨b, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_mul, hb, map_one, mul_inv_cancel₀ h0]

end PI.OkpW
