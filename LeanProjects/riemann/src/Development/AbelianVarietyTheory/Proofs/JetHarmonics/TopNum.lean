import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopNum

theorem hsq_le (r : ℕ) (T b C : ℝ) (hC : 0 ≤ C) (hb : 2 ≤ b)
    (hT : T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ))) :
    Hsq r T b ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h1 : (1 : ℝ) ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hb1 (mul_nonneg hC (Nat.cast_nonneg _))
  have h2 : max 1 T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) := max_le h1 hT
  have h3 : (C + 10) * ((2 * r + 2 : ℕ) : ℝ)
      = C * ((2 * r + 2 : ℕ) : ℝ) + ((20 * (r + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.rpow_add hb0, Real.rpow_natCast]
  unfold Hsq
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hb0.le _)

theorem top_num : ∀ (r : ℕ) (T T' b C : ℝ), 0 ≤ C → 2 ≤ b → T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → T' ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → Real.sqrt (Hsq r T b * Hsq r T' b) ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  intro r T T' b C hC hb hT hT'
  have hb0 : 0 < b := by linarith
  have h1 := hsq_le r T b C hC hb hT
  have h2 := hsq_le r T' b C hC hb hT'
  have hp : 0 ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb0.le _
  have h0 : 0 ≤ Hsq r T' b := by
    unfold Hsq
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hb0.le _)
  rw [Real.sqrt_le_left hp, sq]
  exact mul_le_mul h1 h2 h0 hp

end GlobalTheory.TopNum
