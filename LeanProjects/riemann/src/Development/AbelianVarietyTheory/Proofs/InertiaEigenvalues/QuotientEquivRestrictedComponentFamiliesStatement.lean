import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientEquivRestrictedComponentFamilies
import Mathlib
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_equiv_restrictedComponentFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  first | exact @GlobalTheory.quotient_equiv_restrictedFamilies | exact GlobalTheory.quotient_equiv_restrictedFamilies | (intros; apply GlobalTheory.quotient_equiv_restrictedFamilies <;> assumption)
