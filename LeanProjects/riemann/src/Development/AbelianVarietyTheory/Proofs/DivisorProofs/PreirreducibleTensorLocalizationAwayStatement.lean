import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preirreducible_tensor_localization_away : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  first | exact @GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | exact GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | (intros; apply GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway <;> assumption)
