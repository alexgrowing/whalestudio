import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomain
import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (exact GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (intros; apply GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain  <;> assumption)
