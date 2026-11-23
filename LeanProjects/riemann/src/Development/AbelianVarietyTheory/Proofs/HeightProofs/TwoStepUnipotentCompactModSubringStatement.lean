import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Mathlib
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStepUnipotent_compact_mod_subring : ∀ (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S] (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S), Continuous st → (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → (∀ x ∈ S₀, st x ∈ S₀) → e₁ ∈ S₀ → h ∈ S₀ → e₁ * e₁ = e₁ → st e₁ = e₃ → e₁ * e₃ = 0 → e₃ * e₁ = 0 → h + h = 1 → (∀ x, h * x = x * h) → IsCompact K → (∀ x, ∃ y ∈ S₀, x - y ∈ K) → ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) → ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧ γ * g ∈ K' := by
  first | exact @GlobalTheory.TwoStepUnipotent.compact_mod_subring | exact GlobalTheory.TwoStepUnipotent.compact_mod_subring | (intros; apply GlobalTheory.TwoStepUnipotent.compact_mod_subring <;> assumption)
