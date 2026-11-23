import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightNormSqSmoothPos
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_norm_sq_smooth_pos : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → ∀ y ∈ Y, ∀ lam : Fin n → ℝ,
      ContDiffAt ℝ 2 (weightNormSq H π A lam) y ∧ 0 < weightNormSq H π A lam y := by
  first | exact @GlobalTheory.WeightSmooth.weightNormSq_contDiffAt_pos | exact GlobalTheory.WeightSmooth.weightNormSq_contDiffAt_pos | (intros; apply GlobalTheory.WeightSmooth.weightNormSq_contDiffAt_pos <;> assumption)
