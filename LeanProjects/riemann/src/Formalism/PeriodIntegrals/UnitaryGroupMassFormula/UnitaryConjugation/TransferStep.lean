import Mathlib
import Formalism.PeriodIntegrals.UMultOne

noncomputable section

namespace PI.UConjT

open Matrix

def OnbReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
    Module.finrank ℂ E = m → ∀ T : E →ₗ[ℂ] E, (∀ x y, inner ℂ (T x) (T y) = inner ℂ x y) →
    ∀ e : E, ∃ b : Fin m → E, Orthonormal ℂ b ∧ (∀ i, ∃ c : ℂ, T (b i) = c • b i) ∧
      ∀ i, (inner ℂ (b i) e).im = 0

def SpecReal : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ →
    ∃ u ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∃ d : Fin (n + 1) → ℂ,
      g * u = u * Matrix.diagonal d ∧ ∀ i, (u (Fin.last n) i).im = 0

def TransferStep : Prop := OnbReal → SpecReal

def BlockStep : Prop := SpecReal → PI.UMultOne.ConjTranspose

end PI.UConjT
