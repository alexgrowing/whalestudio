import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarev_degree_one : GlobalTheory.Published.ChebotarevDegreeOne := by
  first | exact @GlobalTheory.Published.chebotarevDegreeOne' | exact GlobalTheory.Published.chebotarevDegreeOne' | (intros; apply GlobalTheory.Published.chebotarevDegreeOne' <;> assumption)
