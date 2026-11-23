import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEuler
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_shape_of_tate_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  first | exact @GlobalTheory.ShapeNeg.shapeG_of_localDuality | exact GlobalTheory.ShapeNeg.shapeG_of_localDuality | (intros; apply GlobalTheory.ShapeNeg.shapeG_of_localDuality <;> assumption)
