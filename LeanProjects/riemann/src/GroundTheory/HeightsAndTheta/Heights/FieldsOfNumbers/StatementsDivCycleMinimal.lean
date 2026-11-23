import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleMinimal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), P.IsPrime →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ a : MRing ι F, a ∉ P →
    ∀ (W : Ideal (MRing ι F)) (hW : W.IsPrime), relDim W = (n : ℕ) → P ⊔ Ideal.span {a} ≤ W →
      haveI := hW
      W ∈ (P ⊔ Ideal.span {a}).minimalPrimes ∧ multAt (P ⊔ Ideal.span {a}) W ≠ ⊤

end

end GroundTheory.Heights₂.Heights.FieldNumbers
