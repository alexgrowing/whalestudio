import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCongruenceFiltrationFiniteTowerBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E T : ℕ) (G : ℕ → Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Antitone G → G 0 ≤ lowerRamificationGroup K L 0 → ¬ G 0 ≤ G 1 → (∀ σ ∈ G 0, σ ^ p ∈ G 1) → (∀ j, j + 1 ≤ 2 * T + 8 → ∀ σ ∈ G 0, σ ^ p ∈ G (j + 1) → σ ∈ G j) → (∀ k ≤ 2 * T, Detects p 8 (G k) (G (k + 8))) → 2 ^ T * Nat.card ↥(G 0) < E := by
  first | exact @GlobalTheory.PMon.Ram.finiteTowerBound | exact GlobalTheory.PMon.Ram.finiteTowerBound | (intros; apply GlobalTheory.PMon.Ram.finiteTowerBound <;> assumption)
