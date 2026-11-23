import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantFormEqSumInvariantTensors
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  first | exact @GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | exact GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | (intros; apply GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors <;> assumption)
