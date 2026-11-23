import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_holds : Sa2.PropPlane := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.plane | exact GlobalTheory.CompanionTheory.PlaneSA.plane | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.plane <;> assumption)
