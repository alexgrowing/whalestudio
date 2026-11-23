import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDual
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open ReciprocityTheory.PGsh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ) (u : Fin i → Fin d → C), IsSatFrame v u → ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧ ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  first | exact @GlobalTheory.FrameDual.frameDual | exact GlobalTheory.FrameDual.frameDual | (intros; apply GlobalTheory.FrameDual.frameDual <;> assumption)
