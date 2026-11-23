import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem prod_pow_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  intro v f k r m a b x hv hm ha hb hlo hhi
  have hv0 : 0 < v := by linarith
  have hw1 : 1 ≤ 8 * v := by linarith
  have hw0 : 0 < 8 * v := by linarith
  have hvw : v ≤ 8 * v := by linarith
  have hvf : 0 ≤ v ^ f := by positivity
  have key : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m *
        (ENNReal.ofReal (v ^ f) ^ b * ENNReal.ofReal y ^ m)) =
      ENNReal.ofReal (v ^ (k * m * f) * (v ^ (f * (a + m + b)) * y ^ m)) := by
    intro y hy
    rw [← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hy,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [Real.rpow_neg hw0.le, Real.rpow_natCast] at hlo
  rw [Real.rpow_natCast] at hhi
  constructor
  · refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hlo _) _) _)
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 1 ≤ v ^ (f * (a + m + b)) := one_le_pow₀ hv
    have h2 : ((8 * v) ^ (2 * (r + 1) ^ 2 * f))⁻¹ ≤ ((8 * v) ^ f)⁻¹ ^ m := by
      rw [inv_pow, ← pow_mul]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ hw1
      rw [mul_comm f m]
      apply Nat.mul_le_mul_right
      nlinarith
    exact h2.trans (le_mul_of_one_le_left (by positivity) h1)
  · refine le_trans (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hhi _) _) _) ?_
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : v ^ (f * (a + m + b)) ≤ (8 * v) ^ (f * (a + m + b)) :=
      pow_le_pow_left₀ hv0.le hvw _
    calc v ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m
        ≤ (8 * v) ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (8 * v) ^ ((a + m + b + m) * f) := by ring
      _ ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := by
          apply pow_le_pow_right₀ hw1
          apply Nat.mul_le_mul_right
          nlinarith

end GlobalTheory.DegVol.RefCov
