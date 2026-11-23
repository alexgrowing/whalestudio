import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocalRing.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    (IsNoetherianRing (degZeroLoc P {W}) ∧ IsLocalRing (degZeroLoc P {W})) ∧
      ∀ n : ℕ, relDim P = (n + 1 : ℕ) → relDim W = (n : ℕ) → ringKrullDim (degZeroLoc P {W}) = 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
