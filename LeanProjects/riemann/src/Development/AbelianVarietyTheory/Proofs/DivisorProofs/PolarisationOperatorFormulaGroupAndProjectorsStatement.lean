import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationOperator_formula_groupAndProjectors : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  first | exact @GlobalTheory.PolarFormula.polar_formula | exact GlobalTheory.PolarFormula.polar_formula | (intros; apply GlobalTheory.PolarFormula.polar_formula <;> assumption)
