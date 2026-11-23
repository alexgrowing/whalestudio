import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem volume_product_le : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  intro r R₀ De hr hR hD
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hm : 2 * ((s + 1) * (s + 1 - 1) / 2) ≤ (s + 1) * s := by
    rw [Nat.add_sub_cancel]; omega
  generalize (s + 1) * (s + 1 - 1) / 2 = m at hm ⊢
  have e1 : 4 * (s + 1) - 2 = 4 * s + 2 := by omega
  have e2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e1, e2]
  have hx : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hr
  generalize ((s + 1 : ℕ) : ℝ) = x at hx ⊢
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have h24 : (2 : ℝ) ≤ 4 := by norm_num
  have hms : 2 * m * s ≤ (s + 1) * s * s := Nat.mul_le_mul_right s hm
  calc _ ≤ ((4 : ℝ) * (R₀ ^ (2 * (s + 1)) * De) ^ 2) ^ m * ((4 * (x * R₀ ^ (4 * s + 2) * De ^ 2) ^ 2) ^ m * (4 * (x * R₀ ^ (4 * s + 2) * De ^ 2)) ^ (s + 1)) * ((4 * (x * R₀ ^ (2 * s + 1) * De) ^ 2) ^ (3 * (s + 1)) * 4 * (x * R₀ ^ (2 * s + 1) * De) ^ (2 * (s + 1) ^ 2 + 2 * (s + 1)) * 4 ^ ((s + 1) ^ 2)) := by
        gcongr
    _ = (4 : ℝ) ^ (2 * m + (s + 1) + 3 * (s + 1) + 1 + (s + 1) ^ 2) *
          x ^ (2 * m + (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          R₀ ^ (4 * (s + 1) * m + (4 * s + 2) * 2 * m + (4 * s + 2) * (s + 1) + (2 * s + 1) * 2 * (3 * (s + 1)) + (2 * s + 1) * (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          De ^ (6 * m + 2 * (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) := by
        simp only [mul_pow, ← pow_mul]
        generalize (4 : ℝ) = c
        ring
    _ ≤ (4 : ℝ) ^ (11 * (s + 1) ^ 2) * x ^ (11 * (s + 1) ^ 2) * R₀ ^ (20 * (s + 1) ^ 3) * De ^ (12 * (s + 1) ^ 2) := by
        have h4 : (1 : ℝ) ≤ 4 := by norm_num
        gcongr
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s), Nat.zero_le (s * s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
    _ = _ := by rw [mul_pow]

end GlobalTheory.Amp
