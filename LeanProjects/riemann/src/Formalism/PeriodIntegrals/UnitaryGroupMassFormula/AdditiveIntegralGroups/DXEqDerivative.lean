import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem omega_mul_Gv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = -1 := by
  have hw1 := wq_const h
  have hder := dX_eq_derivative wq
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq ^ 2 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 6 * wq ^ 3 := h
  have hD := congrArg (PowerSeries.derivative ℂ_[p]) h'
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at hD
  have hQ : PowerSeries.constantCoeff
      (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := by
      rw [show (2 : PowerSeries ℂ_[p]) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    simp [hw1, h2]
  have key : (-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative ℂ_[p] wq) *
      (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
        2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1) =
      -(wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) := by
    linear_combination (PowerSeries.X : PowerSeries ℂ_[p]) * hD
  calc omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)
      = ((-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative ℂ_[p] wq) *
        (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
          2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1)) *
        (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2))⁻¹ := by
        simp only [omegaW, Gv, wser, hder]
        ring
    _ = -1 := by
        rw [key, neg_mul, PowerSeries.mul_inv_cancel _ hQ]

end PI.AddIntG.Wk
