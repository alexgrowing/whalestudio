import Formalism.TruncatedSeriesCounting.AprimeArith

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma sigma_exponent_le_real (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j : ℕ) (hj : 1 ≤ j) :
    (sigE ℓ g h j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hjm : m + 1 - 1 = m := by omega
  unfold sigE
  rw [hjm]
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hA0 : (0 : ℝ) ≤ (h : ℝ) + 2 * g := by positivity
  have hP1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hPq : ((ℓ : ℝ) - 1) ^ m ≤ (ℓ : ℝ) ^ m := pow_le_pow_left₀ hq0.le (by linarith) m
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ m := by linarith
  have hM : (Mpar ℓ g h : ℝ) ≤ ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1 := by
    unfold Mpar
    push_cast
    have hc : (((ℓ - 1 : ℕ)) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    rw [hc] at this
    push_cast at this
    linarith
  have hM0 : (0 : ℝ) ≤ (Mpar ℓ g h : ℝ) := by positivity
  have hr : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hq2]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    positivity
  have hceil := Nat.ceil_lt_add_one hX0
  have e1 : ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
      3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) +
        (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
    field_simp
  have t1 : 3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) ≤ 9 / 4 * g := by nlinarith
  have t2 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) + 3 / 4 := by
    have hB : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by positivity
    have s1 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
        (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      gcongr
    have s2 : (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m =
        ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) +
          ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      field_simp
    have s3 : ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) ≤
        3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hB]
      have k1 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m := by
        have : (ℓ : ℝ) ≤ 3 / 2 * ((ℓ : ℝ) - 1) := by linarith
        calc (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) ^ m :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left hPq (by positivity)
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hA0 hq2.le)
      have e2 : ((ℓ : ℝ) - 1) ^ (m + 1 + 1) = ((ℓ : ℝ) - 1) ^ m * ((ℓ : ℝ) - 1) ^ 2 := by ring
      rw [e2]
      nlinarith [k2]
    have s4 : ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤ 3 / 4 := by
      rw [div_le_iff₀ hP0]
      nlinarith
    linarith
  rw [e1] at hceil ⊢
  linarith

theorem total_exponent_le_eight_hundred : ExponentBoundOfRankAndKappaBounds := by
  intro ℓ hℓ G g h j ell rr kap hj hG hg hgh hell hrr hkap
  have hσ := sigma_exponent_le_real ℓ hℓ g h j hj
  unfold eE a0E
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hB4 : (4 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (ℓ : ℝ) - 1) (by omega : 2 ≤ j + 1)
    nlinarith
  have hB0 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (j + 1) := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGg : (G : ℝ) ≤ g := by exact_mod_cast hG
  have hgh' : (g : ℝ) ≤ h := by exact_mod_cast hgh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hT : (0 : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) := by positivity
  have hΛ : (0 : ℝ) ≤ Real.logb ℓ h := Real.logb_nonneg (by linarith) hh1
  have hlog2 : Real.logb ℓ (2 * h) = Real.logb ℓ 2 + Real.logb ℓ h :=
    Real.logb_mul (by norm_num) (by positivity)
  have hl2 : Real.logb ℓ 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le (by linarith : (1 : ℝ) < ℓ) (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ ℓ)
    rwa [Real.logb_self_eq_one (by linarith)] at this
  have hGL : (G : ℝ) / ℓ ≤ g / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hgB : (g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ g / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hB4
  have h4g : 4 * (g : ℝ) / ((ℓ : ℝ) - 1) ≤ 2 * g := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eσ : 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) =
      3 / 2 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) + 3 * ((g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) := by
    ring
  rw [eσ] at hσ
  rw [hlog2] at hkap
  have hge : (g : ℝ) ≤ g * ell := by nlinarith
  have hee : (ell : ℝ) ≤ g * ell := by nlinarith
  have h1e : (1 : ℝ) ≤ g * ell := by nlinarith
  nlinarith

end Formalism.TruncatedSeriesCounting.WachCoordinates
