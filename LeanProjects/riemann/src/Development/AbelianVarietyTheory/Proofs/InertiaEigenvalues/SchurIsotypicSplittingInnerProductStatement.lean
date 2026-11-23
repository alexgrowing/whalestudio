import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurIsotypicSplittingInnerProduct
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_isotypic_splitting_inner_product : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  first | exact @GlobalTheory.schur_isotypic_splitting | exact GlobalTheory.schur_isotypic_splitting | (intros; apply GlobalTheory.schur_isotypic_splitting <;> assumption)
