import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEquivariantMapsProportional
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_equivariant_maps_proportional : ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ := by
  first | exact @GlobalTheory.schur_proportional | exact GlobalTheory.schur_proportional | (intros; apply GlobalTheory.schur_proportional <;> assumption)
