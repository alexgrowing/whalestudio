import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOne
import Mathlib
open MeasureTheory
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_orthogonality_subgroup_measure_one : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G] (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G), MeasurableSet (Ω : Set G) → ν (Ω : Set G) = 1 → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W), (∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) → (∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ) → (∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ a a' x x' : W, IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧ (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | exact GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | (intros; apply GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality <;> assumption)
