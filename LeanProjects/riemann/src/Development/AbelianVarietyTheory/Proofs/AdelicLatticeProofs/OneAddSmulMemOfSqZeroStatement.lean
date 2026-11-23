import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneAddSmulMemOfSqZero
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_smul_mem_of_sq_zero' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  first | exact @GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | exact GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | (intros; apply GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero <;> assumption)
