import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticSimpleRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (y : Fin d → ℂ) (τ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) y) →
    τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ AnalyticOnNhd ℂ ψ U ∧ ψ y = τ ∧
        ∀ y' ∈ U, ψ y' ∈ B ∧ ∀ s ∈ B, (s ^ N + ∑ j, a j y' * s ^ (j : ℕ) = 0 ↔ s = ψ y')

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
