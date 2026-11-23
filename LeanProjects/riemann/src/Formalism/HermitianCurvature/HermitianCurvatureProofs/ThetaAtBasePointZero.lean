import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem theta_at_base_point_zero : th TT α (x0 TT) = 0 := by
  simp [th, prim_eq]

theorem exp_base_point_eq (hTT : 0 ≤ TT) : Complex.exp (x0 TT) = ((TT + 1 : ℝ) : ℂ) := by
  rw [x0, ← Complex.ofReal_exp, Real.exp_log (by linarith)]

theorem circleMap_eq (hTT : 0 ≤ TT) (θ : ℝ) : circleMap 0 (TT + 1) θ = Complex.exp (x0 TT + (θ : ℂ) * I) := by
  simp [circleMap, Complex.exp_add, exp_base_point_eq hTT]

theorem vert_mem (hTT : 0 ≤ TT) (θ : ℝ) : x0 TT + (θ : ℂ) * I ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT + (θ : ℂ) * I))
  rw [Complex.exp_add, exp_base_point_eq hTT, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  nlinarith

theorem circleIntegral_eq (hTT : 0 ≤ TT) :
    circleIntegral α 0 (TT + 1) = ∫ θ in (0 : ℝ)..2 * Real.pi, I * bet α (x0 TT + (θ : ℂ) * I) := by
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, smul_eq_mul, circleMap_eq hTT θ, bet]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
