import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetChangeOfBases
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_change_of_basis' : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' → Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  first | exact @GlobalTheory.gram_det_change_of_bases | exact GlobalTheory.gram_det_change_of_bases | (intros; apply GlobalTheory.gram_det_change_of_bases <;> assumption)
