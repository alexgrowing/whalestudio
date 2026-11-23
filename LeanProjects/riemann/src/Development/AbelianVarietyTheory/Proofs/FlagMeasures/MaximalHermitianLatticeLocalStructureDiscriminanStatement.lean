import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_local_structure_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → (badP h M).Finite ∧ discN h M = ∏ᶠ P ∈ badP h M, Ideal.absNorm P ∧ Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ᶠ P ∈ badP h M, P)) ∧ ∀ P ∈ badP h M, conjIdeal (K := K) P = P ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 ∧ ∃ x ∈ M, (∃ a : 𝓞 K, (a : K) = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧ ∀ y ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, y - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by
  first | exact @GlobalTheory.MaxLatStruct.main | exact GlobalTheory.MaxLatStruct.main | (intros; apply GlobalTheory.MaxLatStruct.main <;> assumption)
