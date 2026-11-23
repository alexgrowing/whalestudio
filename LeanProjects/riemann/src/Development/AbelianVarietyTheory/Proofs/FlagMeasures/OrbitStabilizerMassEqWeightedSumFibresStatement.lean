import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres : ∀ (G α β : Type) [Group G] [MulAction G α] [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) → Stable G X → Stable G Y → Set.MapsTo π X Y → (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) → orbMass G X = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  first | exact @GlobalTheory.Mass.orbMass_eq_orbSum_fibre | exact GlobalTheory.Mass.orbMass_eq_orbSum_fibre | (intros; apply GlobalTheory.Mass.orbMass_eq_orbSum_fibre <;> assumption)
