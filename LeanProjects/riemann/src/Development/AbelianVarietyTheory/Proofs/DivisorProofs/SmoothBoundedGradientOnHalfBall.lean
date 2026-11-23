import Mathlib
open scoped ContDiff

namespace GlobalTheory

theorem sq_pi_norm_le_sum_sq {e : ℕ} (w : Fin e → ℂ) : ‖w‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 := by
  have hS : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
  have h : ‖w‖ ≤ Real.sqrt (∑ k, ‖w k‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    have hi : ‖w i‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have := Real.abs_le_sqrt hi
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  calc ‖w‖ ^ 2 ≤ (Real.sqrt (∑ k, ‖w k‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hS

theorem smooth_polydisc_value_fderiv_bound :
    ∀ {e : ℕ} (f : (Fin e → ℂ) → ℝ), ContDiffOn ℝ ∞ f (Metric.ball (0 : Fin e → ℂ) 1) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2), |f z| ≤ C ∧
        ∀ w : Fin e → ℂ, (fderiv ℝ f z w) ^ 2 + (fderiv ℝ f z (Complex.I • w)) ^ 2 ≤
          C * ∑ k, ‖w k‖ ^ 2 := by
  intro e f hf
  have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : Metric.closedBall (0 : Fin e → ℂ) (1 / 2) ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  have hd : ContinuousOn (fderiv ℝ f) (Metric.ball (0 : Fin e → ℂ) 1) :=
    hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by exact_mod_cast le_top)
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn (hd.mono hsub)
  refine ⟨max B₀ (2 * B₁ ^ 2), le_max_of_le_right (by positivity), fun z hz => ⟨?_, fun w => ?_⟩⟩
  · have := hB₀ z hz
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have hz1 := hB₁ z hz
    have key : ∀ v : Fin e → ℂ, (fderiv ℝ f z v) ^ 2 ≤ B₁ ^ 2 * ‖v‖ ^ 2 := by
      intro v
      have h1 : |fderiv ℝ f z v| ≤ B₁ * ‖v‖ := by
        have := (fderiv ℝ f z).le_opNorm v
        rw [Real.norm_eq_abs] at this
        exact this.trans (mul_le_mul_of_nonneg_right hz1 (norm_nonneg _))
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow] at h2
      exact h2
    have hI : ‖Complex.I • w‖ = ‖w‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have hS : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
    have hw := sq_pi_norm_le_sum_sq w
    calc (fderiv ℝ f z w) ^ 2 + (fderiv ℝ f z (Complex.I • w)) ^ 2
        ≤ B₁ ^ 2 * ‖w‖ ^ 2 + B₁ ^ 2 * ‖Complex.I • w‖ ^ 2 := add_le_add (key w) (key _)
      _ = (2 * B₁ ^ 2) * ‖w‖ ^ 2 := by rw [hI]; ring
      _ ≤ (2 * B₁ ^ 2) * ∑ k, ‖w k‖ ^ 2 := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ max B₀ (2 * B₁ ^ 2) * ∑ k, ‖w k‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) hS

end GlobalTheory
