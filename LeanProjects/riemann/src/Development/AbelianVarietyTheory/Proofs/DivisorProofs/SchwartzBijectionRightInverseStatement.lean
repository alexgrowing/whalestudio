import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bijection_right_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  first | exact @GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | exact GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | (intros; apply GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse <;> assumption)
