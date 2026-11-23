import Mathlib

theorem UpperTheory.Reformulated.B.Yia3.main :
    ∀ (r : ℝ), (0 : ℝ) < r → ∀ (k : ℕ), (↑(r ^ (2 : ℕ)) : ℂ) ^ ((↑k : ℂ) / (2 : ℂ)) = (↑r : ℂ) ^ k := by
  intro r hr k
  have hr2 : (0 : ℝ) ≤ r ^ (2 : ℕ) := by positivity
  have hcast : ((↑k : ℂ) / (2 : ℂ)) = (((k : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_cpow hr2]
  have hreal : (r ^ (2 : ℕ)) ^ ((k : ℝ) / 2) = r ^ k := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    have : ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hreal]
  push_cast
  rfl
