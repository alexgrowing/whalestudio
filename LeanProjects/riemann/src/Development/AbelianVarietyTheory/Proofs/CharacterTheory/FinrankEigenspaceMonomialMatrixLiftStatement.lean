import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinrankEigenspaceMonomialMatrixLift
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigenspace_monomial_matrix_lift : ∀ (k : Type) [Field k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → ∀ μ : k, μ ≠ 0 → Module.finrank k (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) = Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  first | exact @GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift | exact GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift | (intros; apply GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift <;> assumption)
