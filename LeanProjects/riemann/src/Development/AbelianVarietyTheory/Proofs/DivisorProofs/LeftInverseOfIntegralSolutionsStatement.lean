import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseOfIntegralSolutions
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_inverse_of_integral_solutions : ∀ (V Fr : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] (n m : ℕ) (A : Matrix (Fin n) (Fin m) V), (∀ (cf : Fin m → Fr) (b : Fin n → V), (A.map (algebraMap V Fr)).mulVec cf = (fun j => algebraMap V Fr (b j)) → ∀ i, ∃ a : V, algebraMap V Fr a = cf i) → ∃ B : Matrix (Fin m) (Fin n) V, B * A = 1 := by
  first | exact @GlobalTheory.dvr_matrix_exists_leftInverse_of_saturated | exact GlobalTheory.dvr_matrix_exists_leftInverse_of_saturated | (intros; apply GlobalTheory.dvr_matrix_exists_leftInverse_of_saturated <;> assumption)
