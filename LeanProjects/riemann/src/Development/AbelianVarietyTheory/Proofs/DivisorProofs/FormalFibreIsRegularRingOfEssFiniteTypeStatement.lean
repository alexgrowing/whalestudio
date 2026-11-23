import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingOfEssFiniteType
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  first | exact @GlobalTheory.formalFibre_isRegularRing_of_essFiniteType | exact GlobalTheory.formalFibre_isRegularRing_of_essFiniteType | (intros; apply GlobalTheory.formalFibre_isRegularRing_of_essFiniteType <;> assumption)
