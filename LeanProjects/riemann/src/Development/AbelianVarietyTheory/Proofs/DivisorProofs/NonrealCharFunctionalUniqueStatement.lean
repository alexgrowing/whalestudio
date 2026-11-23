import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonrealCharFunctionalUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonreal_char_functional_unique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar χ →
    (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((χ ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (s : ℝ) (ℓ : Fin a → k), ℓ ≠ 0 →
    ∀ L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y : Matrix (Fin a) (Fin (a + b)) k, Matrix.vecMul ℓ Y = 0 → Ψ.1 Y = 0) → L Ψ = 0) →
      (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
        L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) →
      L = 0 := by
  first | exact @GlobalTheory.LineZeroForm.conjForm_eq_zero | exact GlobalTheory.LineZeroForm.conjForm_eq_zero | (intros; apply GlobalTheory.LineZeroForm.conjForm_eq_zero <;> assumption)
