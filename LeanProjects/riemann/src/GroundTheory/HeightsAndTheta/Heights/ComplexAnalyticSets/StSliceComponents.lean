import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceComponents.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u ℓ : Fin n → ℂ),
    IsProjPrime J → (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      Set.InjOn (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) ((divCycle J u).support : Set _) ∧
        (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) '' ((divCycle J u).support : Set _) =
          (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes ∧
        ∀ W ∈ (divCycle J u).support,
          localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
              (W ⊔ Ideal.span {linForm ℓ - 1}) = divCycle J u W

end

end GroundTheory.Heights₂.Heights
