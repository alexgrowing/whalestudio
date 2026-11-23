import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))

def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)

def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2

def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩

end GlobalTheory.CompanionTheory.FSCrofton
