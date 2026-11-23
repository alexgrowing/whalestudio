import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitianLattices_glued_subspace_complement : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (e e' : ℕ), IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → (∃ t : Finset ↥U, t.card ≤ e ∧ dual (hRes h U) A = A ⊔ Submodule.span (𝓞 K) (t : Set _)) → (∃ t : Finset ↥(perp h U), t.card ≤ e' ∧ dual (hRes h (perp h U)) B = B ⊔ Submodule.span (𝓞 K) (t : Set _)) → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ (((discN (hRes h U) A * discN (hRes h (perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.Glue.main | exact GlobalTheory.Mass.Glue.main | (intros; apply GlobalTheory.Mass.Glue.main <;> assumption)
