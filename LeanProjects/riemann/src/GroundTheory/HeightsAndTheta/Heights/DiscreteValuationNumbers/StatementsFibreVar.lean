import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (MRing ι O), divCycle P (C ϖ) W ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
