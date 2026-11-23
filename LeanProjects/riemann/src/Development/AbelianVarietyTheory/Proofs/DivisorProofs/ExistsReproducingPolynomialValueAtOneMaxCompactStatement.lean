import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact : GlobalTheory.PsCo.Pc3.Repro := by
  first | exact @GlobalTheory.PsCo.Pc3.fock_reproducing_formula | exact GlobalTheory.PsCo.Pc3.fock_reproducing_formula | (intros; apply GlobalTheory.PsCo.Pc3.fock_reproducing_formula <;> assumption)
