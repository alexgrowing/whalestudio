import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocSeparate.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, ¬ W₁ ≤ W₂ →
      ∃ x ∈ degZeroLoc P 𝒲, (¬ ∃ y ∈ degZeroLoc P {W₁}, x * y = 1) ∧
        ∃ y ∈ degZeroLoc P {W₂}, x * y = 1

section Example

abbrev lineOtherPointIdeal : Ideal LineRing := Ideal.span {X ⟨(), (1 : Fin 2)⟩}

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
