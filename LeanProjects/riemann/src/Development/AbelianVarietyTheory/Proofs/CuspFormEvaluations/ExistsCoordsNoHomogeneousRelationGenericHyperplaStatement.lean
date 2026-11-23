import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  first | exact @GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | exact GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | (intros; apply GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero <;> assumption)
