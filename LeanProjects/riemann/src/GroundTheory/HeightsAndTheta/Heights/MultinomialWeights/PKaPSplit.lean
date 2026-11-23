import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem KaPSplit.proof : KaPSplit.Statement := by
  intro d p φ hp _ hs τ
  have h2 : ∀ n : ℕ, ((φ ^ (n + 1)) (τ, false)).2 = false := by
    intro n
    induction n with
    | zero => simpa using hs τ
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have e : (φ ^ (n + 1)) (τ, false) = (((φ ^ (n + 1)) (τ, false)).1, false) :=
        Prod.ext rfl ih
      rw [e]
      exact hs _
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) =
      (d.j : ℝ) * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n) := by
    intro n
    simp only [rankLie, h2 n, Bool.false_eq_true, if_false]
    rw [pow_succ, mul_inv, inv_pow]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  unfold kaP
  rw [tsum_congr hterm, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e1 : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [e1]
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
