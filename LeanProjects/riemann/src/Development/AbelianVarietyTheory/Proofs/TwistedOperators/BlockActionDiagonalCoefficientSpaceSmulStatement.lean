import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul : ∀ {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ) (Q : Formalism.L2.DIV.Pol ℂ ι n), Q ∈ Formalism.L2.DIV.VV ℂ lam → Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q = (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  first | exact @GlobalTheory.blockAct_diag_mem_VV | exact GlobalTheory.blockAct_diag_mem_VV | (intros; apply GlobalTheory.blockAct_diag_mem_VV <;> assumption)
