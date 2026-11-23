import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ M', IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsUnimodular h M → IsMaxLat h M ∧ badP h M = ∅ ∧ lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), IsOrthoLattice h M n → Submodule.IsLattice K M ∧ IsUnimodular h M ∧ Module.finrank K V = n) := by
  first | exact @GlobalTheory.Mass.MaxExists.main | exact GlobalTheory.Mass.MaxExists.main | (intros; apply GlobalTheory.Mass.MaxExists.main <;> assumption)
