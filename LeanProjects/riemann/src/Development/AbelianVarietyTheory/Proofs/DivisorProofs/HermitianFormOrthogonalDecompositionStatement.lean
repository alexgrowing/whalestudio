import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormOrthogonalDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_orthogonal_decomposition : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0) →
    ∀ (W : Submodule ℂ V), W ≤ D → ∀ (s : Finset V), (↑s ⊆ (D : Set V)) →
    (∀ w ∈ W, ∃ z ∈ Submodule.span ℂ (s : Set V), B (w - z) (w - z) = 0) →
    ∀ u ∈ D, ∃ a ∈ W, ∀ w ∈ W, B w (u - a) = 0 := by
  first | exact @GlobalTheory.exists_orthogonal_proj_of_finite_mod_radical | exact GlobalTheory.exists_orthogonal_proj_of_finite_mod_radical | (intros; apply GlobalTheory.exists_orthogonal_proj_of_finite_mod_radical <;> assumption)
