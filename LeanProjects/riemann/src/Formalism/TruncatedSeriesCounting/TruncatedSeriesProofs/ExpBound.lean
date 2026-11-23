import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma lam_ge_one (ℓ H : ℕ) (hℓ : 2 ≤ ℓ) : 1 ≤ lam ℓ H := by
  unfold lam
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have h2 : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg h1 h2
    linarith

private lemma hcoef_le (x : ℝ) (hx : 11 ≤ x) :
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd0 : (0 : ℝ) < x - 1 := by linarith
  have ht : (0 : ℝ) ≤ x - 11 := by linarith
  have ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 2]
  have hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hx2 : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  have e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2) := by ring
  have e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2) := by ring
  linarith

theorem expBound_statement : ExpBound := by
  intro ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2
  have hx : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < ℓ := by linarith
  have hL := lam_ge_one ℓ (h + η) (by omega)
  have hc := hcoef_le (ℓ : ℝ) hx
  have hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1 := by
    unfold sig
    push_cast
    ring
  have hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h1
  rw [hsig]
  unfold sig₂ at he2 ⊢
  unfold aR at ha
  set L := lam ℓ (h + η) with hLdef
  set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef
  have hhH : (h : ℝ) ≤ H := by
    rw [hHdef]
    push_cast
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hbH : (b : ℝ) ≤ H := le_trans (by exact_mod_cast hbh) hhH
  have hH0 : 0 ≤ H := by positivity
  have hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [sq, ← div_div]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)
  have hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤
      (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) :=
    div_le_div_of_nonneg_right ha hd0.le
  have hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hbH (by positivity)
  have hHc := mul_le_mul_of_nonneg_left hc hH0
  have e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) =
      H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3) := by
    rw [div_div, ← pow_succ, mul_div_assoc]
  have hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  have hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hd
  have hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
  have hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1) := by positivity
  have k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) =
      2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) =
      3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by
    ring
  have k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) =
      H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) +
        L / ((ℓ : ℝ) - 1) := by
    ring
  have k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) =
      ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 +
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) =
      8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) +
        H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    ring
  have k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2) := by ring
  have k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2) := by ring
  have k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by ring
  rw [k1] at hs1
  rw [k2] at hE
  rw [k3] at hA
  rw [k5] at hHc
  rw [k6] at he2
  rw [k4, k6, k7, k8]
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
