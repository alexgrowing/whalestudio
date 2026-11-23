import Mathlib
import Formalism.PeriodIntegrals.LatDefs
import Formalism.PeriodIntegrals.SigmaStarEx

noncomputable section

open Complex

namespace PI.SSE

def th (τ u : ℂ) : ℂ := cexp (Real.pi * I * u) * jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ

def ThetaDerivNe : Prop :=
  ∀ τ : ℂ, 0 < τ.im → 3 ≤ 4 * τ.im ^ 2 → jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0

def ReduceBasis : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧
    PI.lat2 v₁ v₂ = PI.lat2 w₁ w₂ ∧ 0 < (v₂ / v₁).im ∧ 3 ≤ 4 * (v₂ / v₁).im ^ 2

end PI.SSE

end
