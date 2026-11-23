import Formalism.TruncatedSeriesCounting.AprimeArith

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma log_nat_le (h : ℕ) : Real.log h ≤ (h : ℝ) / 1000 + 998 := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · have hx : (0 : ℝ) < h := by exact_mod_cast hpos
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < h / 1000 by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000 by norm_num)
    rw [Real.log_div hx.ne' (by norm_num)] at h1
    linarith

private lemma mpar_le (ℓ g h : ℕ) (hℓ : 11 ≤ ℓ) :
    (Mpar ℓ g h : ℝ) ≤ ((h:ℝ) + 2 * g) / 10 + 1 := by
  have hk : (10 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ ℓ - 1)
  have h1 : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hk
  have h3 := h1.trans h2
  rw [Mpar, Nat.cast_add, Nat.cast_one]
  push_cast at h3 ⊢
  linarith

private lemma sig_lt (ℓ g h j : ℕ) (hℓ : 11 ≤ ℓ) :
    (sigE ℓ g h j : ℝ) < 11 / 100 * (3 * (g:ℝ) + ((h:ℝ) + 2 * g) / 10 + 1) + 2 := by
  unfold sigE
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hM := mpar_le ℓ g h hℓ
  have hM0 : (0 : ℝ) ≤ Mpar ℓ g h := Nat.cast_nonneg _
  have hpow : (1 : ℝ) ≤ (ℓ : ℝ) ^ (j - 1) := one_le_pow₀ (by linarith)
  have hq : (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ Mpar ℓ g h := div_le_self hM0 hpow
  have hfrac : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 11 / 100 := by
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (by linarith : (0 : ℝ) ≤ 11 * ℓ - 1)]
  set A := 3 * (g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hx0 : 0 ≤ A * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc := Nat.ceil_lt_add_one hx0
  have hAl : A * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ A * (11 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hfrac hA0
  have hA : A ≤ 3 * g + ((h : ℝ) + 2 * g) / 10 + 1 := by rw [hAdef]; linarith
  linarith

private lemma rr_le (ℓ G h j : ℕ) (rr : ℝ) (hℓ : 11 ≤ ℓ) (hj : 1 ≤ j)
    (hrr : rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)) :
    rr ≤ 20 * ((G : ℝ) / 11 + (h : ℝ) / 100 + ((h : ℝ) / 1000 + 998) + 1) := by
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : (G : ℝ) / ℓ ≤ G / 11 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl
  have hp : (100 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have h10 : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
    calc (100 : ℝ) = 10 ^ 2 := by norm_num
      _ ≤ ((ℓ : ℝ) - 1) ^ 2 := by gcongr
      _ ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ h / 100 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
  have hlog0 : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hlogl : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h3 : Real.logb ℓ h ≤ Real.log h := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h4 := log_nat_le h
  linarith

theorem exists_constant_exponent_inequalities : AprimeArith := by
  refine ⟨100000, by norm_num, ?_⟩
  intro ℓ hℓ b w S η j ell b₀ b₁ rr hj hC hell hb0 hb0' hb1 hb1' hrr
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hG0 : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := Nat.cast_nonneg _
  have hjG : (0 : ℝ) ≤ (j : ℝ) * ((w + S + η : ℕ) : ℝ) := by positivity
  have hbig : (200000 : ℝ) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b := by nlinarith
  have hbG : w + S + η + 1 < b := by
    have : (((w + S + η + 1 : ℕ)) : ℝ) < b := by push_cast at hbig ⊢; linarith
    exact_mod_cast this
  have hb1r : (b : ℝ) ≤ b₁ := by exact_mod_cast hb1
  have hb0r : (b₀ : ℝ) ≤ b + η := by exact_mod_cast hb0'
  have hηG : (η : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by exact_mod_cast (by omega : η ≤ w + S + η)
  have hlb : (11 : ℝ) * b₁ ≤ ℓ * b₁ := mul_le_mul_of_nonneg_right hl (by positivity)
  refine ⟨by omega, by omega, by linarith, by linarith, ?_⟩
  have hs := sig_lt ℓ (max (w + S + η) 1) (b + η + S) j hℓ
  have hr := rr_le ℓ (w + S + η) (b + η + S) j rr hℓ hj hrr
  have hg : ((max (w + S + η) 1 : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : max (w + S + η) 1 ≤ w + S + η + 1)
  have hg0 : (0 : ℝ) ≤ ((max (w + S + η) 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hellr : (ell : ℝ) ≤ 3 * j + 1 := by exact_mod_cast hell
  have hge : ((max (w + S + η) 1 : ℕ) : ℝ) * ell ≤ (((w + S + η : ℕ) : ℝ) + 1) * (3 * j + 1) :=
    mul_le_mul hg hellr (Nat.cast_nonneg _) (by positivity)
  have hH : ((b + η + S : ℕ) : ℝ) ≤ b + ((w + S + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b + η + S ≤ b + (w + S + η))
  unfold a0E
  nlinarith
