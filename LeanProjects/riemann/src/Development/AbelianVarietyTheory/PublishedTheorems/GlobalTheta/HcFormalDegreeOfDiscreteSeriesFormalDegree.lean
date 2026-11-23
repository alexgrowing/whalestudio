import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscreteSeriesWithDegree

open MeasureTheory Matrix Finset Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesFormalDegree : Prop :=
  ∀ (c : CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (F : SignFrame ε P Q) (lam : Fin n → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),

      ((CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) π ∧ IsIrredOn (UJset ε) π ∧ IsSqIntOn ε π) ∧

        HasInfChar ε (fun a => (lam a : ℂ)) π ∧

        (∃! S : Submodule ℂ H, IsKTypeOf ε π (lam + rhoN ε - rhoC ε) S) ∧

        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε π μ S →
          ∃ k : Fin n → Fin n → ℕ, (∀ a b, k a b ≠ 0 → a < b) ∧
            μ = (lam + rhoN ε - rhoC ε) + ∑ a, ∑ b, (k a b : ℝ) • root a b) ∧

      IsFdeg (cdMeasure c F) π
        ((∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
          ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)))

end GlobalTheory.Published
