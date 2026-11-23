import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfect
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K], (∀ a : Λ, algebraMap (Localization.AtPrime P) K (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  first | exact @GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | exact GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | (intros; apply GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial <;> assumption)
