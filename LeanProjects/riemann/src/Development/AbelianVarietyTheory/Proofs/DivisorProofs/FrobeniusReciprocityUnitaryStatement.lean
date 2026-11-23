import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusReciprocityUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_reciprocity_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin a) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∃ (L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ) (χ : kˣ →* ℂˣ) (s : ℝ), (χ = ν ∨ χ = ν⁻¹) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Ψ₁, Bf Ψ₁ Ψ₂ = 0) → L Ψ₂ = 0) ∧
        (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
          Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
          L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), L Ψ₂ = 0 → ∃ U ∈ nhds (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))),
          ∀ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) := by
  first | exact @GlobalTheory.BlockDiagonalOmegaIdentities.frobenius_X0 | exact GlobalTheory.BlockDiagonalOmegaIdentities.frobenius_X0 | (intros; apply GlobalTheory.BlockDiagonalOmegaIdentities.frobenius_X0 <;> assumption)
