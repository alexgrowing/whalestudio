import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ → ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | exact GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | (intros; apply GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem <;> assumption)
