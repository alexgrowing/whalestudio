import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_of_separable_charPoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl := by
  first | exact @GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable | exact GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable | (intros; apply GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable <;> assumption)
