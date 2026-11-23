import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVR
import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_uniformiser_isDVR) | (exact GlobalTheory.adjoinRoot_uniformiser_isDVR) | (intros; apply GlobalTheory.adjoinRoot_uniformiser_isDVR  <;> assumption)
