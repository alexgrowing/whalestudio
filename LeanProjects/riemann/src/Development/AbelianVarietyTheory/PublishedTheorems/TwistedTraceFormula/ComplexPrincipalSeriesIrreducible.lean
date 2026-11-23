import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace GlobalTheory.LeviFactor
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace

namespace GlobalTheory.Published

def ComplexPrincipalSeriesIrreducible : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' → (∀ i, W i ∈ Set.range W') →
    W' (Fin.last b) = W (Fin.last a) →
    ∀ (χ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) (y : Fin b → ℝ), IsURepOn (mats (leviOne ε W' ⊓ slPart ε W)) χ →
      ∀ μ : Measure ↥(KG ε ⊓ slPart ε W), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
          (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X))
          (ι : indFun (slPart ε W) (fun _ => 1) W' χ (fun l => Complex.I * y l) →ₗ[ℂ] X),
          IsIndModel (slPart ε W) (KG ε ⊓ slPart ε W) μ _ ρ ι ∧ IsIrredOn (mats (slPart ε W)) ρ

end GlobalTheory.Published

end
