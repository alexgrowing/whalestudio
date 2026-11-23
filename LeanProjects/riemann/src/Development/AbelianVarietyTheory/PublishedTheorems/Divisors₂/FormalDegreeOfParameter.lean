import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame

noncomputable section

namespace GlobalTheory.Published

def FormalDegreeOfParameter : Prop :=
  ∀ (c : CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (F : SignFrame ε P Q) (lam : Fin n → ℝ), IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsHCDS ε lam π → IsFdeg (cdMeasure c F) π (dimV lam)

end GlobalTheory.Published

end
