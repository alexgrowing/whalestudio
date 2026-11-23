import Mathlib
import Formalism.PeriodIntegrals.SchurFock
import Formalism.PeriodIntegrals.HwIrred

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

instance instMeasurableSpaceMat (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _

instance instBorelSpaceMat (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩

def evalM {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s

def EvalOne : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam, evalM 1 s = normFock lam s (extremal ℂ N lam)

def IsHaarU (N : ℕ) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, x ∈ Matrix.unitaryGroup (Fin N) ℂ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (x * u) ∂μ = ∫ x, f x ∂μ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (u * x) ∂μ = ∫ x, f x ∂μ)

def HaarU : Prop := ∀ N : ℕ, ∃ μ : Measure (Matrix (Fin N) (Fin N) ℂ), IsHaarU N μ

def SchurOrth : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)), IsHaarU N μ →
    ∀ s ∈ nablaSq ℂ N lam,
      (normFock lam s s).re = (Module.finrank ℂ (delSq ℂ N lam) : ℝ) * ∫ x, ‖evalM x s‖ ^ 2 ∂μ

end PI.WSF
