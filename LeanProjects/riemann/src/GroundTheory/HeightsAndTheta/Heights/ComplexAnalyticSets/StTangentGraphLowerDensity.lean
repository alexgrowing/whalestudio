import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))) (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
    I₀.card = d → IsOpen Ω → IsOpen V → w₀ ∈ Ω → DifferentiableOn ℂ g Ω →
    (∀ w ∈ Ω, frameProj b I₀ (g w) = w) → S ∩ V = g '' Ω →
    (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) →
    ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (θ * ρ ^ (2 * d)) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) ≤
        μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ)

def TangentGraphLowerDensity.axisMap : (↥({0} : Finset (Fin 2)) → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 =>
      if j = 0 then ContinuousLinearMap.proj (⟨0, Finset.mem_singleton_self 0⟩ : ↥({0} : Finset (Fin 2)))
      else 0)

theorem TangentGraphLowerDensity.unitBall_pos (d : ℕ) :
    0 < μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  rw [h]
  exact Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self one_pos⟩

end

end GroundTheory.Heights₂.Heights
