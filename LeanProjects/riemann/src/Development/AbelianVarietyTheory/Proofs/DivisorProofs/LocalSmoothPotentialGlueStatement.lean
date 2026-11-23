import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSmoothPotentialGlue
open scoped ContDiff Topology
open Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_smooth_potential_glue : ∀ {e : ℕ} (N c : (Fin e → ℂ) → ℝ) (B : Set (Fin e → ℂ)), IsOpen B → Dense {z | c z ≠ 0} → (∀ z0 ∈ B, ∃ V : Set (Fin e → ℂ), IsOpen V ∧ z0 ∈ V ∧ ∃ F : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ F V ∧ ∀ z ∈ V ∩ B, N z = c z * Real.exp (-F z)) → ∃ f : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ f B ∧ ∀ z ∈ B, N z = c z * Real.exp (-f z) := by
  first | exact @GlobalTheory.smooth_local_exp_glue | exact GlobalTheory.smooth_local_exp_glue | (intros; apply GlobalTheory.smooth_local_exp_glue <;> assumption)
