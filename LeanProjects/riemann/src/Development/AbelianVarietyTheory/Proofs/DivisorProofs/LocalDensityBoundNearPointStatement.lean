import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_bound_near_point : ∀ (d : ℕ) (T : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))) (ρ : ReciprocityTheory.L2DbarEstimates.V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : ReciprocityTheory.L2DbarEstimates.V (d + 1)),
    IsOpen T → z₀ ∈ T → ContinuousOn ρ T → ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) T →
    (∀ z ∈ T, (G (GlobalTheory.LineCos.base z)).PosDef) →
    ∃ N : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.exists_map_cosSq_le | exact GlobalTheory.LineCos.exists_map_cosSq_le | (intros; apply GlobalTheory.LineCos.exists_map_cosSq_le <;> assumption)
