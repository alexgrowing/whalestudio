import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq

noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cm_norm_eq_one (D : D7) (μ : D.host.E) (h : star μ * μ = 1) (φ : D.host.E →+* ℂ) :
    ‖φ μ‖ = 1 := by
  have hφ := D.sp.cm.cmUnram.2.1 φ μ
  have h1 : φ (star μ) * φ μ = 1 := by rw [← map_mul, h, map_one]
  rw [hφ, Complex.conj_mul'] at h1
  have h2 : ‖φ μ‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : 0 ≤ ‖φ μ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖φ μ‖ - 1), sq_nonneg (‖φ μ‖ + 1)]

theorem cm_norm_eq_one' (D : D7) (μ : D.host.E) (h : μ * star μ = 1) (φ : D.host.E →+* ℂ) :
    ‖φ μ‖ = 1 := cm_norm_eq_one D μ (by rw [mul_comm]; exact h) φ

end PI.UnitaryGroupMassFormula.BetaLUniq
