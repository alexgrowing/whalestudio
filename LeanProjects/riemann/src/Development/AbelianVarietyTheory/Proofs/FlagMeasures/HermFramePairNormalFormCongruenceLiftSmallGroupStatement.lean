import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔫 : Ideal (𝓞 K), (∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) → ∀ s ∈ N.R, (∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) → ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧ ∀ x ∈ N.P0, s' x - x ∈ 𝔫 • N.P0 := by
  first | exact @GlobalTheory.DegCnt.LiftS.lift_congruence | exact GlobalTheory.DegCnt.LiftS.lift_congruence | (intros; apply GlobalTheory.DegCnt.LiftS.lift_congruence <;> assumption)
