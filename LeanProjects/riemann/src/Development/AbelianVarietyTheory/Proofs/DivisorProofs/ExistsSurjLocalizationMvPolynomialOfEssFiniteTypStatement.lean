import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local : ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime) (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  first | exact @GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | exact GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | (intros; apply GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType <;> assumption)
