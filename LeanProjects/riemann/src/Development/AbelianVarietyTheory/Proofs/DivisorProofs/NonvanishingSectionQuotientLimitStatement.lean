import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSectionQuotientLimit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_section_quotient_limit : ∀ (B : Type) [TopologicalSpace B] (b₀ : B) (J : Type) (O : J → Set (B × ℝ × ℝ)) (s : J → B × ℝ × ℝ → ℂ) (K : Set (ℝ × ℝ)), IsCompact K → (∀ i, IsOpen (O i)) → (∀ q, ∃ i, q ∈ O i) → (∀ i, ∀ q ∈ O i, s i q ≠ 0) → (∀ i, ContinuousOn (fun v : ℝ × ℝ => s i (b₀, v)) {v | (b₀, v) ∈ O i}) → (∀ i j, ContinuousOn (fun q => s i q / s j q) (O i ∩ O j)) → ∃ V ∈ nhds b₀, ∃ r : B × ℝ × ℝ → ℂ, (∀ q ∈ V ×ˢ K, r q ≠ 0) ∧ ∀ i, ContinuousOn (fun q => s i q * r q) (O i ∩ V ×ˢ K) := by
  first | exact @GlobalTheory.frame_extend_near_fibre | exact GlobalTheory.frame_extend_near_fibre | (intros; apply GlobalTheory.frame_extend_near_fibre <;> assumption)
