import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineBcrisBasicTheorems_proof : GlobalTheory.Published.FontaineBcris := by
  first | exact @GlobalTheory.MemLoc.fontaineBcris | exact GlobalTheory.MemLoc.fontaineBcris | (intros; apply GlobalTheory.MemLoc.fontaineBcris <;> assumption)
