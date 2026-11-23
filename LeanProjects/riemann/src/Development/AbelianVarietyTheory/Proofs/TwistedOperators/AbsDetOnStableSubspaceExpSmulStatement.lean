import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absDetOnStableSubspace_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ, GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  first | exact @GlobalTheory.FlagMeas.detOn_exp_smul | exact GlobalTheory.FlagMeas.detOn_exp_smul | (intros; apply GlobalTheory.FlagMeas.detOn_exp_smul <;> assumption)
