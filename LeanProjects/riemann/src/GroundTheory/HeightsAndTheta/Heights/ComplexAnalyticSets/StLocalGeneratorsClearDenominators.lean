import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime

def LocalGeneratorsClearDenominators.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T),
    (∀ i, f i ∈ P) →
    maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 →
      ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
