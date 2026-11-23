import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTensorLocalizationInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_tensor_localization_injective' : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    letI := Localization.AtPrime.algebraOfLiesOver (Q.under (integralClosure S L)) Q
    Function.Injective (algebraMap (Localization.AtPrime (Q.under (integralClosure S L))) (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.integralClosure_tensor_localization_injective) | (exact GlobalTheory.integralClosure_tensor_localization_injective) | (intros; apply GlobalTheory.integralClosure_tensor_localization_injective  <;> assumption)
