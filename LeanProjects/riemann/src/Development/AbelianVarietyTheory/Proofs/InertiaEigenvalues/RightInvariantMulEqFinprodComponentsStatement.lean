import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightInvariantMulEqFinprodComponents
import Mathlib
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightInvariant_mul_eq_finprod_components : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) → ∀ g, a g = ∏ᶠ v, a (c v g) := by
  first | exact @GlobalTheory.finprod_components_of_rightInvariant_mul | exact GlobalTheory.finprod_components_of_rightInvariant_mul | (intros; apply GlobalTheory.finprod_components_of_rightInvariant_mul <;> assumption)
