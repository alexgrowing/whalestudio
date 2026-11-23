import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxGenerator
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_generator : Sa2.PropGen := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.propGen | exact GlobalTheory.CompanionTheory.SaGen.propGen | (intros; apply GlobalTheory.CompanionTheory.SaGen.propGen <;> assumption)
