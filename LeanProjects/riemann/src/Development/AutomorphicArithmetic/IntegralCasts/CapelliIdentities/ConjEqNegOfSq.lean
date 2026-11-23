import Mathlib

theorem UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq :
    ∀ {z : ℂ} {d : ℕ},
    (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro z d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    simpa [pow_two] using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im h
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
