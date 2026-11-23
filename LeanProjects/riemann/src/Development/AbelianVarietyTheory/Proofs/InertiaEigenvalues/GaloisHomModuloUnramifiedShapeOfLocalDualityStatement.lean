import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  first | exact @GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | exact GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | (intros; apply GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality <;> assumption)
