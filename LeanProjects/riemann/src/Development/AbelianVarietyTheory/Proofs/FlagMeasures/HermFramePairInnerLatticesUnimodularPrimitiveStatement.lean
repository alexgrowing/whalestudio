import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsUnimodMod H (latL N.F N.F' Λ) (uPerp N.F N.F') (II N.F N.F') ∧ IsUnimodMod H (latL N.F' N.F Λ) (uPerp N.F N.F') (II N.F N.F') ∧ (∀ t : K, t • N.F.z ∈ latL N.F N.F' Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ (∀ t : K, t • N.F'.z ∈ latL N.F' N.F Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ Submodule.IsLattice K (N.Ref (latL N.F N.F' Λ)) ∧ N.Ref (latL N.F N.F' Λ) ⊓ rs (𝓞 K) (V0 N.F N.F') = N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') := by
  first | exact @GlobalTheory.DegCnt.InnerLat.main | exact GlobalTheory.DegCnt.InnerLat.main | (intros; apply GlobalTheory.DegCnt.InnerLat.main <;> assumption)
