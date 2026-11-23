import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

theorem BoundedHomogeneousZero.proof : BoundedHomogeneousZero.Statement.{u} := by
  intro X D g ⟨C, hC⟩ hD

  have iter : ∀ (k : ℕ) (x : X), g (D^[k] x) = 4 ^ k * g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hD, ih, pow_succ]
      ring
  funext x
  simp only [Pi.zero_apply]
  by_contra hx
  have hpos : 0 < |g x| := abs_pos.mpr hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / |g x|) (by norm_num : (1 : ℝ) < 4)
  have hle : (4 : ℝ) ^ k * |g x| ≤ C := by
    have := hC (D^[k] x)
    rwa [iter, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k)] at this
  have : C < (4 : ℝ) ^ k * |g x| := (div_lt_iff₀ hpos).mp hk
  linarith

end GroundTheory.Heights₂.Heights
