import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_fockModel_unitary_dual_pair : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_pair | exact GlobalTheory.nonempty_fockData_pair | (intros; apply GlobalTheory.nonempty_fockData_pair <;> assumption)
