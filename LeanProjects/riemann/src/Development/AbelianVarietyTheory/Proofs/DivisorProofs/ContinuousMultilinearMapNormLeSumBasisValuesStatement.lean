import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  first | exact @GlobalTheory.continuousMultilinear_norm_le_basis_sum | exact GlobalTheory.continuousMultilinear_norm_le_basis_sum | (intros; apply GlobalTheory.continuousMultilinear_norm_le_basis_sum <;> assumption)
