import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

def TorusInvLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (u : ((Σ k, ι k) → ℂ) → ℝ),
    ContDiffOn ℝ 2 u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z) →
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w : (Σ k, ι k) → ℂ,
      |leviForm u z w| ≤
        C * leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w

def TorusInvLevi.projectiveLineModulusRatio (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  ‖z ⟨(), 0⟩‖ ^ 2 / (‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2)

end GroundTheory.Heights₂.Heights.Inter
