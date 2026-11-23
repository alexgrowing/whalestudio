import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_add_vector_det_valuation : AddVec := by
  first | exact @GlobalTheory.InertZeta.addVec | exact GlobalTheory.InertZeta.addVec | (intros; apply GlobalTheory.InertZeta.addVec <;> assumption)
