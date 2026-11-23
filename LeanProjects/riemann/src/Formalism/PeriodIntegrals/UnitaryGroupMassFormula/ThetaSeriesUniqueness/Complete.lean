import Mathlib
import Formalism.PeriodIntegrals.LatDefs
import Formalism.PeriodIntegrals.SigmaStarUniq
import Formalism.PeriodIntegrals.AreaLat

noncomputable section

namespace PI.SSU

open Complex

def coef (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0:ℝ)..1, f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x))

def ShiftInv : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  ∀ (w : ℂ) (n : ℤ),
    (∫ x in (0:ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))) = coef f n

def Complete : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  (∀ n, coef f n = 0) → f = 0

def KeyP : Prop := ∀ (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ), Differentiable ℂ f → K ≠ 0 →
  (k = 1 ∨ k = -1) → (∀ u, f (u + 1) = f u) →
  (∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) → coef f 0 = 0 → f = 0

def FE (A ω p : ℂ) (F : ℂ → ℂ) : Prop := ∀ z, F (z + ω) * Complex.exp
    (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / A - (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A)) =
    p * F z

def normF (a A l : ℂ) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  F (a * u) * Complex.exp (-((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * u ^ 2 - l * u)

def cst (a b τ A l : ℂ) : ℂ :=
  -((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * τ ^ 2 - l * τ +
    (Real.pi : ℂ) * b * (starRingEnd ℂ) b / (2 * A)

end PI.SSU
