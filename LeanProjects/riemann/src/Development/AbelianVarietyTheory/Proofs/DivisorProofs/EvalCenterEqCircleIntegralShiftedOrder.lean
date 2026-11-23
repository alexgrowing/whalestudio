import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem eval_center_eq_circleIntegral_shifted_order : ∀ {X : Type} (s₀ : ℂ) (k k₀ : ℕ) (r : ℝ) (V : Set ℂ) (Eis H H₀ : ℂ → X → ℂ), 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → (∀ g, DifferentiableOn ℂ (H · g) V) → (∀ g, DifferentiableOn ℂ (H₀ · g) V) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H₀ s g = (s - s₀) ^ k₀ * Eis s g) →
    ∀ g, H s₀ g = (2 * ↑Real.pi * Complex.I)⁻¹ * circleIntegral (fun z => (z - s₀) ^ ((k : ℤ) - k₀ - 1) * H₀ z g) s₀ r := by
  intro X s₀ k k₀ r V Eis H H₀ hr hV hball hH hH₀ hHE hH₀E g
  have hdc : DiffContOnCl ℂ (H · g) (Metric.ball s₀ r) :=
    ((hH g).mono (by
      intro z hz; exact hball (Metric.closure_ball_subset_closedBall hz))).diffContOnCl
  have hc := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (Metric.mem_ball_self hr)
  simp only [smul_eq_mul] at hc
  rw [← hc]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hzV : z ∈ V := hball (Metric.sphere_subset_closedBall hz)
  have hne : z - s₀ ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_eq_norm, h0, norm_zero] at hz
    exact hr.ne' hz.symm
  have hz' : z ≠ s₀ := sub_ne_zero.mp hne
  simp only
  rw [hHE z hzV hz' g, hH₀E z hzV hz' g]
  rw [← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_add₀ hne, ← zpow_add₀ hne]
  congr 2
  ring

end GlobalTheory
