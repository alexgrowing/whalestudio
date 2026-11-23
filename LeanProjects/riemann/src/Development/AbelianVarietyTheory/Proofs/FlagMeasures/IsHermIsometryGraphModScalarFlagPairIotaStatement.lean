import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIota
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermIsometryGraphModScalar_flagPairIota : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsModIso H (g : 𝓞 K) (flagPairDefinitePartLattice N.F' N.F Λ) (flagPairDefinitePartLattice N.F N.F' Λ) (iotaGraph N.F N.F' Λ (g : 𝓞 K)) := by
  first | exact @GlobalTheory.ModIdent.isModIso_iota | exact GlobalTheory.ModIdent.isModIso_iota | (intros; apply GlobalTheory.ModIdent.isModIso_iota <;> assumption)
