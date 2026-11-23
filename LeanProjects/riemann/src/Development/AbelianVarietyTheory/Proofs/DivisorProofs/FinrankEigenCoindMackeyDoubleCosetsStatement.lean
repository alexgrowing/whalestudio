import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenCoindMackeyDoubleCosets
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigen_coind_mackey_double_cosets : ∀ (G : Type) [Group G] (P U : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (σ : Representation ℂ P V) (χ : G → ℂ), χ 1 = 1 → (∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') → ∀ (ι : Type) [Fintype ι] (x : ι → G), (∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') → (∀ g : G, (∃ i : ι, ∃ p ∈ P, ∃ u ∈ U, g = p * x i * u) ∨ ∃ y : G, (∃ p ∈ P, ∃ u ∈ U, g = p * y * u) ∧ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) = ⊥) → finrank ℂ (eig (Representation.coind P.subtype σ) (U : Set G) χ) = ∑ i : ι, finrank ℂ (eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i))) := by
  first | exact @GlobalTheory.FinGL.MackeyCosets.finrank_eig_coind | exact GlobalTheory.FinGL.MackeyCosets.finrank_eig_coind | (intros; apply GlobalTheory.FinGL.MackeyCosets.finrank_eig_coind <;> assumption)
