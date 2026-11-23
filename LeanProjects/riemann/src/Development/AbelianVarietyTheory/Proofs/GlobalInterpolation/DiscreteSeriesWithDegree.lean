import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

open MeasureTheory Matrix Finset Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesWithDegree : Prop :=
  ∀ (c : CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (F : SignFrame ε P Q) (lam : Fin n → ℝ), IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCDS ε lam π ∧ IsFdeg (cdMeasure c F) π (dimV lam)

end GlobalTheory.Published

namespace GlobalTheory.FormalDegreeFromClassification

open GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

end GlobalTheory.FormalDegreeFromClassification
