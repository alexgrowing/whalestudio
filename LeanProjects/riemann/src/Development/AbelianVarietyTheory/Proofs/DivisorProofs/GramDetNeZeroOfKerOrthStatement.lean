import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetNeZeroOfKerOrth
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_ker_orth' : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A) → (∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) → (∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) → (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  first | exact @GlobalTheory.gram_det_ne_zero_of_ker_orth | exact GlobalTheory.gram_det_ne_zero_of_ker_orth | (intros; apply GlobalTheory.gram_det_ne_zero_of_ker_orth <;> assumption)
