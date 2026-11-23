import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalComponentFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b → f ∉ P →
    ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → (C ϖ : MRing ι O) ∈ W →
      IsMultiProjPrime (specialIdeal W) ∧
        ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
