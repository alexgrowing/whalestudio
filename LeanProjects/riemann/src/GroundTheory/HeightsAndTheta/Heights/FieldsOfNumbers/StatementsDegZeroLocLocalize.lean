import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocLocalize.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W ∈ 𝒲, ∀ y ∈ degZeroLoc P {W}, ∃ b ∈ degZeroLoc P 𝒲, ∃ s ∈ degZeroLoc P 𝒲,
      (∃ t ∈ degZeroLoc P {W}, s * t = 1) ∧ y * s = b

end

end GroundTheory.Heights₂.Heights.FieldNumbers
