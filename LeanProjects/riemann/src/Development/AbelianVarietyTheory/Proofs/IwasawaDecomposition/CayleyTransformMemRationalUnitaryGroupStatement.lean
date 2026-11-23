import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | exact GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | (intros; apply GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian <;> assumption)
