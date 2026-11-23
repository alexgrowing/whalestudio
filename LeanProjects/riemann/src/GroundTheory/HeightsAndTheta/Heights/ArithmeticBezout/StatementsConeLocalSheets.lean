import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetCover
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)

def ConeLocalSheets.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
        ∀ x : Fin e → ℂ, eval (Fin.cons 1 x : Fin (e + 1) → ℂ) c ≠ 0 →
          ∃ (U : Set (Fin e → ℂ)) (N : ℕ) (s : Fin N → (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ),
            IsOpen U ∧ x ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
            ∀ y ∈ U, (∀ j, s j y ∈ mcPts P ∧ Ψ (segre (s j y)) = Fin.cons 1 y) ∧
              Function.Injective (fun j => s j y) ∧
              fibre P Ψ y ⊆ Set.range (fun j => segre (s j y))

end GroundTheory.Heights₂.Heights
