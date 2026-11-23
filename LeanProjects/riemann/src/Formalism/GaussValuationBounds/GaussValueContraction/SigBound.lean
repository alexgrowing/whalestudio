import Formalism.GaussValuationBounds.Statement

namespace Formalism.NOK

theorem sigBound_pow (L a : ℝ) (k : ℕ) (hL : 3 ≤ L) (ha : a = L - 1) :
    L * a ^ (k + 2) ≤ 3 / 2 * L ^ k * a ^ 3 := by
  have ha2 : 2 ≤ a := by linarith
  rcases k with _ | k
  · simp only [pow_zero, zero_add, mul_one]
    have : 0 ≤ a ^ 2 := by positivity
    nlinarith
  · have h1 : a ^ k ≤ L ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h3 : 0 < a ^ 3 := by positivity
    have hLp : 0 < L := by linarith
    have e1 : L * a ^ (k + 1 + 2) = L * a ^ k * a ^ 3 := by ring
    have e2 : 3 / 2 * L ^ (k + 1) * a ^ 3 = 3 / 2 * L * L ^ k * a ^ 3 := by ring
    rw [e1, e2]
    have h4 : L * a ^ k * a ^ 3 ≤ L * L ^ k * a ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ h3.le
      exact mul_le_mul_of_nonneg_left h1 hLp.le
    have h5 : 0 ≤ L * L ^ k * a ^ 3 := by positivity
    nlinarith

theorem sigBound_proof : SigBound := by
  intro ℓ hℓ g h j hj
  unfold sigNOK
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hL3 : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  set L : ℝ := (ℓ : ℝ) with hL
  set a : ℝ := L - 1 with ha
  have ha2 : 2 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hLpos : 0 < L := by linarith
  have hmle : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h : ℝ) + 2 * g) / a := by
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    have e : ((ℓ - 1 : ℕ) : ℝ) = a := by
      rw [Nat.cast_sub (by omega)]; simp [ha, hL]
    rw [e] at this; push_cast at this; exact this
  set m : ℕ := (h + 2 * g) / (ℓ - 1) with hm
  set H : ℝ := (h : ℝ) + 2 * g with hH
  have hH0 : 0 ≤ H := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  set P : ℝ := L ^ k with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hPpos : 0 < P := by linarith
  have hpow := sigBound_pow L a k hL3 ha

  have hq : L / a ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t1 : 3 * (g : ℝ) * L / a ^ 2 ≤ 9 / 4 * g := by
    have := mul_le_mul_of_nonneg_left hq hg0
    calc 3 * (g : ℝ) * L / a ^ 2 = 3 * ((g : ℝ) * (L / a ^ 2)) := by ring
      _ ≤ 9 / 4 * (g : ℝ) := by linarith
  have t2 : L / (P * a ^ 2) ≤ 3 / 4 := by
    calc L / (P * a ^ 2) ≤ L / (1 * a ^ 2) := by
          apply div_le_div_of_nonneg_left hLpos.le (by positivity)
          exact mul_le_mul_of_nonneg_right hP1 (by positivity)
      _ = L / a ^ 2 := by ring
      _ ≤ 3 / 4 := hq
  have t3 : H * L / (P * a ^ 3) ≤ 3 / 2 * H / a ^ (k + 1 + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L * a ^ (k + 2) ≤ 3 / 2 * P * a ^ 3 := hpow
    calc H * L * a ^ (k + 1 + 1) = H * (L * a ^ (k + 2)) := by ring
      _ ≤ H * (3 / 2 * P * a ^ 3) := mul_le_mul_of_nonneg_left this hH0
      _ = 3 / 2 * H * (P * a ^ 3) := by ring
  have t4 : (m : ℝ) * L / (P * a ^ 2) ≤ H * L / (P * a ^ 3) := by
    have e : H * L / (P * a ^ 3) = (H / a) * L / (P * a ^ 2) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hmle hLpos.le
  have hsplit : (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 =
      3 * (g : ℝ) * L / a ^ 2 + (m : ℝ) * L / (P * a ^ 2) + L / (P * a ^ 2) := by
    field_simp; ring
  have hX0 : 0 ≤ (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 := by positivity
  have hfl := Nat.floor_le hX0
  push_cast
  rw [hsplit] at hfl ⊢
  linarith

end Formalism.NOK
