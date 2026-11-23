import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGenerators
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairInnerLattice_indices_and_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → (idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) : ℝ) * cardB N.F N.F' Λ = delBar N.F N.F' Λ ∧ idx (latL N.F' N.F Λ) (lamOne N.F N.F' Λ) = idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ∧ lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ ∧ idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≤ cardB N.F N.F' Λ ∧ GenBy (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) N.j := by
  first | exact @GlobalTheory.DegCnt.InnerIndex.main | exact GlobalTheory.DegCnt.InnerIndex.main | (intros; apply GlobalTheory.DegCnt.InnerIndex.main <;> assumption)
