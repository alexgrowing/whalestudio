import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylOrthonormalBasisValuesAtUnitarySumSqLeOn
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n, ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 := by
  first | exact @GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | exact GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | (intros; apply GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one <;> assumption)
