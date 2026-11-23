import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | exact GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | (intros; apply GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra <;> assumption)
