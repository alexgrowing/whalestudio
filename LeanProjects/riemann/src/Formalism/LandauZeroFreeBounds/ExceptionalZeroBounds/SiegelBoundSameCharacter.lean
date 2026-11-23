import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

open Real

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem log_three_mul_le_rpow {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    Real.log (3 * N) ≤ 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
  have h := Real.log_le_rpow_div (x := 3 * N) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN] at h
  have e : (3 : ℝ) ^ (ε / 2) * N ^ (ε / 2) / (ε / 2) = 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
    field_simp
  linarith

theorem siegel_bound_key_rearrange {C A₁ CL x ℓ a K ε q₁ q : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hKa : K * a ≤ ε / 2) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) (hA₁ : 0 ≤ A₁) (hx : 0 ≤ x) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ CL * Real.log (3 * (q₁ * q)))
    (hkey : 1 / 2 - C * (A₁ * x * ℓ) * (q₁ * q) ^ (K * a) / a ≤ 0) :
    a / (2 * (max C 1 * max A₁ 1 * max CL 1 * (2 * (3 : ℝ) ^ (ε / 2) / ε)) * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set Q := q₁ * q with hQ
  set L := 2 * (3 : ℝ) ^ (ε / 2) / ε with hLdef
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hk : a / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) := by
    have h' : 1 / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) / a := by linarith
    rw [le_div_iff₀ ha] at h'; linarith
  have hlog0 : 0 ≤ Real.log (3 * Q) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (3 * Q) ≤ L * Q ^ (ε / 2) := log_three_mul_le_rpow hQ0 hε
  have hℓ' : ℓ ≤ max CL 1 * (L * Q ^ (ε / 2)) :=
    hℓ.trans ((mul_le_mul_of_nonneg_right (le_max_left CL 1) hlog0).trans
      (mul_le_mul_of_nonneg_left hlogL (by positivity)))
  have hQK : Q ^ (K * a) ≤ Q ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hQ1 hKa
  have hW0 : 0 ≤ A₁ * x * ℓ * Q ^ (K * a) := by positivity
  have step1 : C * (A₁ * x * ℓ) * Q ^ (K * a) ≤ max C 1 * (A₁ * x * ℓ * Q ^ (K * a)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left C 1) hW0
  have step2 : A₁ * x * ℓ * Q ^ (K * a)
      ≤ max A₁ 1 * x * (max CL 1 * (L * Q ^ (ε / 2))) * Q ^ (ε / 2) := by
    gcongr
    exact le_max_left A₁ 1
  have hQQ : Q ^ (ε / 2) * Q ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
    rw [← Real.rpow_add (by linarith), add_halves, hQ, Real.mul_rpow (by linarith) (by linarith)]
  set M := max C 1 * max A₁ 1 * max CL 1 * L with hM
  have hM0 : 0 < M := by
    rw [hM]
    have : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max A₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max CL 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hmain : a / 2 ≤ M * x * (q₁ ^ ε * q ^ ε) := by
    have h3 := mul_le_mul_of_nonneg_left step2 (le_trans zero_le_one (le_max_right C 1))
    rw [← hQQ, hM]
    calc a / 2 ≤ _ := hk
      _ ≤ _ := step1
      _ ≤ _ := h3
      _ = _ := by ring
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem siegel_bound_same_character {N₀ : ℕ} (hN₀ : N₀ ≠ 0) {A₁ x ε q₁ q : ℝ} (hε : 0 < ε) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) (hNq : (N₀ : ℝ) = q₁ * q) (hA₁ : 0 < A₁) (hx : 0 ≤ x)
    (hS : A₁ ≤ ((N₀.primeFactors.card : ℝ) + 1) ^ 2 * x) :
    A₁ / (4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set ω := N₀.primeFactors.card with hω

  have hpow : 2 ^ ω ≤ N₀ := by
    have h1 := Finset.pow_card_le_prod N₀.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₀) (Nat.prod_primeFactors_dvd N₀))
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast Nat.pos_of_ne_zero hN₀
  have hpowR : (2 : ℝ) ^ ω ≤ (N₀ : ℝ) := by exact_mod_cast hpow
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hωlog : (ω : ℝ) * Real.log 2 ≤ Real.log N₀ := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpowR
  have hlog2N : Real.log (2 * N₀) = Real.log 2 + Real.log N₀ := Real.log_mul (by norm_num) hN0.ne'
  have hbound := Real.log_le_rpow_div (x := 2 * (N₀ : ℝ)) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN0.le] at hbound
  set R := (2 : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) / (ε / 2) with hR
  have hωR : ((ω : ℝ) + 1) * Real.log 2 ≤ R := by nlinarith
  have hω0 : (0 : ℝ) ≤ (ω : ℝ) + 1 := by positivity
  have hsq : (((ω : ℝ) + 1) * Real.log 2) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hωR 2
  have hR2 : R ^ 2 = 4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε) := by
    have e1 : (2 : ℝ) ^ (ε / 2) * (2 : ℝ) ^ (ε / 2) = (2 : ℝ) ^ ε := by
      rw [← Real.rpow_add (by norm_num), add_halves]
    have e2 : (N₀ : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
      rw [← Real.rpow_add hN0, add_halves, hNq, Real.mul_rpow (by linarith) (by linarith)]
    rw [hR, div_pow, mul_pow, sq ((2 : ℝ) ^ (ε / 2)), sq ((N₀ : ℝ) ^ (ε / 2)), e1, e2]
    field_simp
    ring
  have hT : ((ω : ℝ) + 1) ^ 2 ≤ 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε := by
    have hl22 : 0 < Real.log 2 ^ 2 := by positivity
    rw [mul_pow, hR2] at hsq
    have e : 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε
        = (4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε)) / Real.log 2 ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ hl22]
    exact hsq
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hT hx
  nlinarith

end Formalism.ZeroFreeDirichlet
