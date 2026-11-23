import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisDeterminantUnit
import Mathlib
open NumberField Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_determinant_unit : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (Λ : Submodule (𝓞 E) (Fin N → E)), Submodule.span E (Λ : Set (Fin N → E)) = ⊤ → ∀ φ : La ≃ₗ[𝓞 E] Λ, ∃ a : Fin N → La, ∀ (gam : La ≃ₗ[𝓞 E] La) (τ : E →+* ℂ), IsUnit (Matrix.of fun m l => τ ((φ (gam (a l)) : Fin N → E) m) : Matrix (Fin N) (Fin N) ℂ).det := by
  first | exact @GlobalTheory.lattice_exists_independent_family_all_embeddings | exact GlobalTheory.lattice_exists_independent_family_all_embeddings | (intros; apply GlobalTheory.lattice_exists_independent_family_all_embeddings <;> assumption)
