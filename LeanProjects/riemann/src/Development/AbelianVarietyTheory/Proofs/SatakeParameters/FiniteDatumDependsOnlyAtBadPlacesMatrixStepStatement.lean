import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesMatrixStep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  first | exact @GlobalTheory.AwayMat.ptAway_mat | exact GlobalTheory.AwayMat.ptAway_mat | (intros; apply GlobalTheory.AwayMat.ptAway_mat <;> assumption)
