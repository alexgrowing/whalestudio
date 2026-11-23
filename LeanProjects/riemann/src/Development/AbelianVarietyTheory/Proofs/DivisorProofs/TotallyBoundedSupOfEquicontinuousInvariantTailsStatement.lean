import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTails
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G) (Φ : Set (G → ℂ)), (∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g) → (∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1) → (∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B → ‖φ (g * u) - φ g‖ ≤ ε) → (∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  first | exact @GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | exact GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | (intros; apply GlobalTheory.totallyBounded_sup_of_equicontinuous_tails <;> assumption)
