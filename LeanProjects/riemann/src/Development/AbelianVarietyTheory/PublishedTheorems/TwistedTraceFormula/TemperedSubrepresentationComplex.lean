import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace GlobalTheory.LeviFactor
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace

namespace GlobalTheory.Published

def TemperedSubrepresentationComplex : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' → (∀ i, W i ∈ Set.range W') →
    W' (Fin.last b) = W (Fin.last a) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Nontrivial H → IsURepOn (mats (glPart ε W)) π →
      IsIrredOn (mats (glPart ε W)) π → ∀ ν : Measure (glPart ε W), ν.IsHaarMeasure →
      (∀ v w, IsKFinIn (glPart ε W) π v → IsKFinIn (glPart ε W) π w → ∀ r : ℝ, 0 < r →
        Integrable (fun g : glPart ε W => ‖⟪v, π (uMat g.1) w⟫_ℂ‖ ^ (2 + r)) ν) →
      ∃ (χ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) (y : Fin b → ℝ),
        IsURepOn (mats (leviOne ε W' ⊓ glPart ε W)) χ ∧
        ∀ μ : Measure ↥(KG ε ⊓ glPart ε W), μ.IsHaarMeasure → IsProbabilityMeasure μ →
          ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
            (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X))
            (ι : indFun (glPart ε W) (fun _ => 1) W' χ (fun l => Complex.I * y l) →ₗ[ℂ] X),
            IsIndModel (glPart ε W) (KG ε ⊓ glPart ε W) μ _ ρ ι ∧
            ∃ T : H →ₗᵢ[ℂ] X, ∀ g ∈ glPart ε W, ∀ v, T (π (uMat g) v) = ρ (uMat g) (T v)

end GlobalTheory.Published

end
