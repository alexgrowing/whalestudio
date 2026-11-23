import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant : ∀ {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ),
    GlobalTheory.JSW.schur n (GlobalTheory.JSW.padTo hmn l) = GlobalTheory.JSW.jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  first | exact @GlobalTheory.JSW.schur_padTo_eq_jtDet | exact GlobalTheory.JSW.schur_padTo_eq_jtDet | (intros; apply GlobalTheory.JSW.schur_padTo_eq_jtDet <;> assumption)
