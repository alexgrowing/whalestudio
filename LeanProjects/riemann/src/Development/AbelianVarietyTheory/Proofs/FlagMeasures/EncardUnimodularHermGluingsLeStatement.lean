import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUnimodularHermGluingsLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_unimodular_hermGluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  first | exact @GlobalTheory.DegCnt.Glue.encard_gluings_le | exact GlobalTheory.DegCnt.Glue.encard_gluings_le | (intros; apply GlobalTheory.DegCnt.Glue.encard_gluings_le <;> assumption)
