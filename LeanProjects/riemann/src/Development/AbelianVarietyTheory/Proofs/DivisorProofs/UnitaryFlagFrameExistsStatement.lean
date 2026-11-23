import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFlagFrameExists
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_flag_frame_exists : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → ∃ e, IsUnitaryFlagFrame Y H π A e := by
  first | exact @GlobalTheory.FlagFrame.exists_unitaryFlagFrame | exact GlobalTheory.FlagFrame.exists_unitaryFlagFrame | (intros; apply GlobalTheory.FlagFrame.exists_unitaryFlagFrame <;> assumption)
