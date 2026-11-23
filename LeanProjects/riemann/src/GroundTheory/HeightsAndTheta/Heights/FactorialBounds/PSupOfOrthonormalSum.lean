import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

theorem SupOfOrthonormalSum.proof : SupOfOrthonormalSum.Statement := by
  intro V _ _ ι _ b p hb c

  have h1 : p (∑ i, c i • b i) ≤ ∑ i, ‖c i‖ := by
    refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul_eq_mul]
    calc ‖c i‖ * p (b i) ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
      _ = ‖c i‖ := mul_one _

  have h2 : (∑ i, ‖c i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι) (fun _ => (1 : ℝ))
      (fun i => ‖c i‖)
    simpa [Finset.card_univ] using hcs
  have h3 : ∑ i, ‖c i‖ ≤ √(Fintype.card ι : ℝ) * √(∑ i, ‖c i‖ ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le h2
  exact h1.trans h3

end GroundTheory.Heights₂.Heights
