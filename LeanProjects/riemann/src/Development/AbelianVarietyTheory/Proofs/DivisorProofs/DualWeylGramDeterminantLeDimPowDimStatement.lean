import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDim
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  first | exact @GlobalTheory.OnMatGram.norm_det_onMat_sq_le | exact GlobalTheory.OnMatGram.norm_det_onMat_sq_le | (intros; apply GlobalTheory.OnMatGram.norm_det_onMat_sq_le <;> assumption)
