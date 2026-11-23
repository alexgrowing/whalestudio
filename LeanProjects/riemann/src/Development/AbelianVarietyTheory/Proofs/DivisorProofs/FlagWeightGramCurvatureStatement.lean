import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagWeightGramCurvature
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_weight_gram_curvature : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ (lam : Fin n → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ) (C : ℝ), TwoFormBound U H G (curv H) C →
      FormAbsLe (horizForm H π e lam y) (1 / (2 * Real.pi) * (∑ i, |lam i|) * C) (pullForm G π y) := by
  first | exact @GlobalTheory.horizForm_formAbsLe | exact GlobalTheory.horizForm_formAbsLe | (intros; apply GlobalTheory.horizForm_formAbsLe <;> assumption)
