import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

def NegBound : Prop :=
  ∀ (k r : ℕ) (S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ)),
    (∀ x ∈ S, (herm (Hpk k r) x x).re ≤ 0) → Module.finrank ℂ S ≤ r + 1

def SignQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Prop :=
  ∃ Q : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ, IsUnit Q.det ∧
    Qᴴ * gramM k r z z' γ * Q = Matrix.fromBlocks 1 0 0 (-1)

def SignStep : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 → SignQ k r z z' γ

def UPos : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 → SignQ k r z z' γ →
    ∀ v ∈ Uperp k r z z' γ, v ≠ 0 → 0 < (herm (Hpk k r) v v).re

end PI.FrameInd
