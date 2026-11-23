import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_of_etale_on_punctured_spectrum : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  first | exact @GlobalTheory.PurityStep.free_of_etale_punctured | exact GlobalTheory.PurityStep.free_of_etale_punctured | (intros; apply GlobalTheory.PurityStep.free_of_etale_punctured <;> assumption)
