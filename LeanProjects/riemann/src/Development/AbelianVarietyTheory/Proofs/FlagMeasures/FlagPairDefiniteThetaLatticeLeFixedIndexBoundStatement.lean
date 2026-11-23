import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧ 0 < N.gI g Λ ∧ 0 < N.iI g Λ ∧ (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del ∧ ((N.gI g Λ : ℝ) * N.iI g Λ ≤ N.Del) ∧ GenBy (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K)) N.j ∧ del H (latTh N.F N.F' Λ) = (N.gI g Λ : ℝ) * N.iI g Λ * N.NT ∧ IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') := by
  first | exact @GlobalTheory.DegCnt.FixIdx.main | exact GlobalTheory.DegCnt.FixIdx.main | (intros; apply GlobalTheory.DegCnt.FixIdx.main <;> assumption)
