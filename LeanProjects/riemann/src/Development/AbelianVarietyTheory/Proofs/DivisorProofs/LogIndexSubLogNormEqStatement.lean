import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIndexSubLogNormEq
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_index_sub_log_norm_eq : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (hI : I.FG) (c : K), c ∈ I → c ≠ 0 → Real.log ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) - ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = -Real.log (FractionalIdeal.absNorm (⟨I, FractionalIdeal.isFractional_of_fg hI⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
  first | exact @GlobalTheory.log_relIndex_span_sub_sum_log_eq_neg_log_absNorm | exact GlobalTheory.log_relIndex_span_sub_sum_log_eq_neg_log_absNorm | (intros; apply GlobalTheory.log_relIndex_span_sub_sum_log_eq_neg_log_absNorm <;> assumption)
