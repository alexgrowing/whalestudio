import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def QuasiFiniteSheets.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ y : Fin d → ℂ, (ComplexSets.fibre I A y).Finite) →
      ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y c ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
          IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
          ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre I A y') ∧
            Function.Injective (fun j => s j y') ∧
            ComplexSets.fibre I A y' ⊆ Set.range (fun j => s j y')

end GroundTheory.Heights₂.Heights
