import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectors
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K)) (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K), Continuous q → (∀ (c : K) w, q (c • w) = (c * star c) • q w) → (∀ w ∈ S, q w = 0 → w = 0) → ∀ Q : Set (Matrix (Fin m) (Fin m) K), IsCompact Q → ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  first | exact @GlobalTheory.quadratic_preimage_compact_on_subspace | exact GlobalTheory.quadratic_preimage_compact_on_subspace | (intros; apply GlobalTheory.quadratic_preimage_compact_on_subspace <;> assumption)
