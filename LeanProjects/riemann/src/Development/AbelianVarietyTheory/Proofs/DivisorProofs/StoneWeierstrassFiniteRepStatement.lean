import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneWeierstrassFiniteRep
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stone_weierstrass_finite_rep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Q : Subgroup G), IsCompact (Q : Set G) →
    ∀ (d : ℕ) (ρ : Q →* Matrix (Fin d) (Fin d) ℂ), Continuous ρ → ∀ A : Subalgebra ℂ (G → ℂ), (∀ f ∈ A, Continuous f) → (∀ f ∈ A, star f ∈ A) →
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
      (∀ f ∈ A, ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ f ∈ V ∧ (∀ w ∈ V, w ∈ A) ∧ ∀ w ∈ V, ∀ q ∈ Q, (fun g => w (q * g)) ∈ V) →
      ∀ v : Fin d → ℂ, ∃ f : Fin d → G → ℂ, (∀ i, f i ∈ A) ∧ (∀ i, f i 1 = v i) ∧
        ∀ (q : Q) (g : G), (fun i => f i ((q : G) * g)) = Matrix.mulVec (ρ q) (fun i => f i g) := by
  first | exact @GlobalTheory.exists_equivariant_mem_subalgebra_of_compact | exact GlobalTheory.exists_equivariant_mem_subalgebra_of_compact | (intros; apply GlobalTheory.exists_equivariant_mem_subalgebra_of_compact <;> assumption)
