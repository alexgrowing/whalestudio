import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm

def logR {n : ℕ} (a : ℕ) (t : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0

def Tame {n : ℕ} (a : ℕ) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧ ∀ t : Fin n → ℂ, ‖t‖ < ε → (∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) →
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f t ∧ |f t| ≤ C * Real.log (logR a t) ∧
      ‖fderiv ℝ f t‖ ≤ C * logR a t ^ C * Real.exp (logR a t / 2)

def PshAt0 {n : ℕ} (f : (Fin n → ℂ) → ℝ) : Prop :=
  ContDiffAt ℝ 2 f 0 ∧ ∀ w : Fin n → ℂ, 0 ≤ levi f 0 w

end AnalyticReference.An
