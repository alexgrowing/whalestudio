import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteType
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  first | exact @GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | exact GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | (intros; apply GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType <;> assumption)
