import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (W : Ideal (MRing ι F)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (MRing ι F ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (MRing ι F ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
