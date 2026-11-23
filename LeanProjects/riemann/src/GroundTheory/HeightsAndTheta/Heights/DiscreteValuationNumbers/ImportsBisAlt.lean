import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def BlowUpStrictTransform.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ s : MRing ι O, s ∉ P → ∀ (e : K → ℕ) (m : MRing ι O),
    ∀ H : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      (divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) H ≠ 0 ∨
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) H ≠ 0) →
      divCycle P s (H.comap (liftForm (J := BlowUpIdx ι))) ≠ 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
