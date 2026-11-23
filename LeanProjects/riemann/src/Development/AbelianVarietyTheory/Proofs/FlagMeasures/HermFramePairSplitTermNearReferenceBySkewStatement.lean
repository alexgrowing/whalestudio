import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairSplitTermNearReferenceBySkew
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∀ e : ℕ, 2 ≤ e → 𝔠 ^ e • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ Λ → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 → Λ ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 → ∃ s ∈ N.ZI, N.Near (𝔠 ^ (6 * e + 30)) (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.DualPos.near_of_skew | exact GlobalTheory.DegCnt.DualPos.near_of_skew | (intros; apply GlobalTheory.DegCnt.DualPos.near_of_skew <;> assumption)
