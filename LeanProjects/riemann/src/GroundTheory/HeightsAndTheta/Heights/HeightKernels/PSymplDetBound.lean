import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplDetBound

theorem step_bound (n : ℕ) (ρ : ℝ) (hle : ρ ≤ 2 * ((n : ℝ) + 1)) :
    ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have h0 : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ n := by positivity
  calc ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hle h0
    _ ≤ (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
        push_cast; ring

end PSymplDetBound

theorem SymplDetBound.proof (h1 : SymplStep.Statement) : SymplDetBound.Statement := by
  intro n
  induction n with
  | zero =>
    intro G _ _
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    rw [Matrix.det_isEmpty]
    simp
  | succ n ih =>
    intro G hG hpos
    obtain ⟨ρsq, _, _, hle, P, hP, _, hdet⟩ :=
      h1 n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => ih H hH hHpos)
    exact ⟨P, hP, hdet.trans (PSymplDetBound.step_bound n ρsq hle)⟩

end GroundTheory.Heights₂.Heights
