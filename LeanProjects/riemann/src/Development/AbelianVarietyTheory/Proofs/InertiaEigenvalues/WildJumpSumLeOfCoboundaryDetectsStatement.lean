import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfCoboundaryDetects
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects <;> assumption)
