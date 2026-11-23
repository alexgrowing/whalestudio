import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitaryMatricesFiniteCardLe
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unitary_matrices_finite_card_le : ∀ (D : D7) (n : ℕ), {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧ {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  first | exact @GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le | exact GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le | (intros; apply GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le <;> assumption)
