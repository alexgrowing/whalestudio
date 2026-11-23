import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  first | exact @GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | exact GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | (intros; apply GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int <;> assumption)
