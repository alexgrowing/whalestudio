import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] DerivationMinorOfDetection.polyOriginIdeal_isPrime

def DerivationMinorOfDetection.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) →
    (∀ a : Fin h → Localization.AtPrime P,
      ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
        ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)) →
    (∀ g ∈ P, (∀ D : Derivation ℤ T T, D g ∈ P) →
      algebraMap T (Localization.AtPrime P) g ∈ maximalIdeal (Localization.AtPrime P) ^ 2) →
    ∃ D : Fin h → Derivation ℤ T T, (Matrix.of fun i j => D j (f i)).det ∉ P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
