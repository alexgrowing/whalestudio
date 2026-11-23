import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_of_detects <;> assumption)
