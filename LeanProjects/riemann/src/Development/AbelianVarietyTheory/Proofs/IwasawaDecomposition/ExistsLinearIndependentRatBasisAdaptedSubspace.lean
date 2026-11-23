import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFamily
open Matrix

namespace GlobalTheory

theorem adapted_basis_extension (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ L = g) :
    ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧
      (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧
        ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first
  | exact @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | (apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family ..)

end GlobalTheory
