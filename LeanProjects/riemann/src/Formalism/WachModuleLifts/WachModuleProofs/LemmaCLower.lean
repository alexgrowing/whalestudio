import Formalism.WachModuleLifts.Statement

open Finset

noncomputable section

namespace Formalism.CL

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_le_p_real : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

lemma sum_norm_le {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

lemma term_le (N i k : ℕ) (a b : ℚ_[p]) (ha : ‖a‖ ≤ (p : ℝ) ^ (i / N))
    (hb : ‖b‖ ≤ (p : ℝ) ^ (k / N)) : ‖a * b‖ ≤ (p : ℝ) ^ ((i + k) / N) := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ (p : ℝ) ^ (i / N) * (p : ℝ) ^ (k / N) :=
        mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = (p : ℝ) ^ (i / N + k / N) := by rw [pow_add]
    _ ≤ _ := pow_le_pow_right₀ one_le_p_real (Nat.div_add_div_le_add_div)

theorem content_mul (g : ℕ) (f f' : PowerSeries ℚ_[p]) (hf : Content p g f)
    (hf' : Content p g f') : Content p g (f * f') := by
  intro j
  rw [PowerSeries.coeff_mul]
  apply sum_norm_le _ _ (by positivity)
  intro x hx
  have := term_le (p ^ g) x.1 x.2 _ _ (hf x.1) (hf' x.2)
  rwa [mem_antidiagonal.mp hx] at this

theorem content_one (g : ℕ) : Content p g (1 : PowerSeries ℚ_[p]) := by
  intro j
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · rw [norm_one]; exact one_le_pow₀ one_le_p_real
  · rw [norm_zero]; positivity

theorem content_pow (g : ℕ) (f : PowerSeries ℚ_[p]) (hf : Content p g f) (y : ℕ) :
    Content p g (f ^ y) := by
  induction y with
  | zero => rw [pow_zero]; exact content_one g
  | succ y ih => rw [pow_succ]; exact content_mul g _ _ ih hf

lemma coeff_uu (g j : ℕ) :
    PowerSeries.coeff j (uu p g) = (p : ℚ_[p])⁻¹ * (phiIter p g).coeff j := by
  rw [uu, PowerSeries.coeff_smul, Polynomial.coeff_coe, smul_eq_mul]

lemma phiIter_succ' (g : ℕ) : phiIter p (g + 1) = (phiPoly p).comp (phiIter p g) := by
  unfold phiIter; rw [Function.iterate_succ_apply']

lemma phiIter_one : phiIter p 1 = phiPoly p := by
  rw [phiIter_succ', show phiIter p 0 = Polynomial.X from rfl, Polynomial.comp_X]

lemma coeff_phiPoly (j : ℕ) : (phiPoly p).coeff j =
    (if j = p then 1 else 0) - (p : ℚ_[p]) * (if j = p - 1 then 1 else 0) +
      (if j = 0 then (p : ℚ_[p]) else 0) := by
  simp only [phiPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C]

lemma content_of_unit_one : Content p 1 (uu p 1) := by
  have hp2 := hp.out.two_le
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  intro j
  rw [coeff_uu, phiIter_one, coeff_phiPoly, pow_one]
  by_cases h1 : j = p
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega), h1, Nat.div_self (by omega)]
    simp [norm_inv, Padic.norm_p]
  · rw [if_neg h1]
    have hle : (1 : ℝ) ≤ (p : ℝ) ^ (j / p) := one_le_pow₀ one_le_p_real
    by_cases h2 : j = p - 1
    · rw [if_pos h2, if_neg (by omega)]
      have : (p : ℚ_[p])⁻¹ * (0 - (p : ℚ_[p]) * 1 + 0) = -1 := by
        rw [mul_one, zero_sub, add_zero, mul_neg, inv_mul_cancel₀ hp0]
      rw [this, norm_neg, norm_one]; exact hle
    · rw [if_neg h2]
      by_cases h3 : j = 0
      · rw [if_pos h3]
        have : (p : ℚ_[p])⁻¹ * (0 - (p : ℚ_[p]) * 0 + p) = 1 := by
          rw [mul_zero, sub_zero, zero_add, inv_mul_cancel₀ hp0]
        rw [this, norm_one]; exact hle
      · rw [if_neg h3]; simp

lemma natDegree_phiPoly : (phiPoly p).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_phiPoly, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma coe_phiPoly : ((phiPoly p : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) =
    (p : ℚ_[p]) • uu p 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [uu, phiIter_one, smul_smul, mul_inv_cancel₀ hp0, one_smul]

lemma norm_coeff_phiPoly_pow (i j : ℕ) :
    ‖((phiPoly p) ^ i).coeff j‖ ≤ ((p : ℝ)⁻¹) ^ i * (p : ℝ) ^ (j / p) := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, coe_phiPoly, smul_pow, PowerSeries.coeff_smul,
    smul_eq_mul, norm_mul, norm_pow, Padic.norm_p]
  have := content_pow 1 _ (content_of_unit_one (p := p)) i j
  rw [pow_one] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma cotangentAtUnit_tangentBijection_naturality (i k M : ℕ) (hk : k ≤ i) (hM : 0 < M) : i / M + k ≤ k / M + i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : k < M * (k / M + 1) := Nat.lt_mul_div_succ k hM
  have h2 : (k + d) / M < k / M + d + 1 := by
    rw [Nat.div_lt_iff_lt_mul hM]
    nlinarith
  omega

lemma key (g i j : ℕ) :
    (p : ℝ) ^ (i / p ^ g) * ‖((phiPoly p) ^ i).coeff j‖ ≤ (p : ℝ) ^ (j / p ^ (g + 1)) := by
  by_cases hj : p * i < j
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, norm_zero, mul_zero]
    · positivity
    · calc ((phiPoly p) ^ i).natDegree ≤ i * (phiPoly p).natDegree := Polynomial.natDegree_pow_le
        _ ≤ i * p := Nat.mul_le_mul_left _ natDegree_phiPoly
        _ < j := by rw [mul_comm]; exact hj
  · push Not at hj
    have hpos := hp.out.pos
    have hk : j / p ≤ i := Nat.div_le_of_le_mul hj
    have hn := cotangentAtUnit_tangentBijection_naturality i (j / p) (p ^ g) hk (by positivity)
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    calc (p : ℝ) ^ (i / p ^ g) * ‖((phiPoly p) ^ i).coeff j‖
        ≤ (p : ℝ) ^ (i / p ^ g) * (((p : ℝ)⁻¹) ^ i * (p : ℝ) ^ (j / p)) :=
          mul_le_mul_of_nonneg_left (norm_coeff_phiPoly_pow i j) (by positivity)
      _ = ((p : ℝ) ^ (i / p ^ g + j / p)) / (p : ℝ) ^ i := by
          rw [inv_pow, pow_add]; field_simp
      _ ≤ (p : ℝ) ^ (j / p / p ^ g) := by
          rw [div_le_iff₀ (by positivity), ← pow_add]
          exact pow_le_pow_right₀ one_le_p_real hn

end SlopeTestRemainingChoices

end Formalism.CL
