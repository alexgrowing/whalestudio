import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSumKernelCoboundaryCharLeSixMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_kernel_le_six_mul | exact GlobalTheory.PMon.Ram.jumpSum_kernel_le_six_mul | (intros; apply GlobalTheory.PMon.Ram.jumpSum_kernel_le_six_mul <;> assumption)
