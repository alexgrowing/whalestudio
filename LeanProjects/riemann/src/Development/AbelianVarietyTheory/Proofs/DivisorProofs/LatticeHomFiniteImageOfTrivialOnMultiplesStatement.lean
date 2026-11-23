import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiples
import Mathlib

set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  first | exact @GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | exact GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | (intros; apply GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples <;> assumption)
