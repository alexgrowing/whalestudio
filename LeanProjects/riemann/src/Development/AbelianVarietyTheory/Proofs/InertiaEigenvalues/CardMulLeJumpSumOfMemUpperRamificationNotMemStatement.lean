import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ), lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B → (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | exact GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | (intros; apply GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem <;> assumption)
